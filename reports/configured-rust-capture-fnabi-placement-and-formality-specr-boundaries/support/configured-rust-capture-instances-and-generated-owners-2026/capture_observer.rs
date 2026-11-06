#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::{mir, ty::{self, Ty, TyCtxt, Instance, InstanceKind, TypingEnv, EarlyBinder}};
use rustc_span::{Span, def_id::{DefId, LOCAL_CRATE}};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;
type R<T> = Result<T, String>;

fn origin(tcx: TyCtxt<'_>, span: Span) -> Value {
    let sm=tcx.sess.source_map();
    let expansion: Vec<_>=span.macro_backtrace().map(|e|json!({"kind":format!("{:?}",e.kind),"call_site":sm.span_to_diagnostic_string(e.call_site),"definition_site":sm.span_to_diagnostic_string(e.def_site),"macro_definition":format!("{:?}",e.macro_def_id)})).collect();
    json!({"span":sm.span_to_diagnostic_string(span),"call_site":sm.span_to_diagnostic_string(span.source_callsite()),"expansion":expansion})
}
fn instance_id(tcx: TyCtxt<'_>, i: Instance<'_>) -> String {
    format!("{}|{:?}|{:?}",tcx.def_path_str(i.def_id()),i.def,i.args)
}
fn type_ok<'tcx>(tcx:TyCtxt<'tcx>, t:Ty<'tcx>, template:bool, depth:usize)->R<()> {
    if depth>12 {return Err("type depth exceeds finite admission bound".into());}
    match t.kind() {
        ty::Bool|ty::Char|ty::Int(_)|ty::Uint(_)|ty::Never => Ok(()),
        ty::Tuple(ts)=>{for t in ts.iter(){type_ok(tcx,t,template,depth+1)?;}Ok(())},
        ty::Ref(_,t,_)|ty::RawPtr(t,_)=>type_ok(tcx,*t,template,depth+1),
        ty::Param(_) if template=>Ok(()),
        ty::Adt(adt,args) if adt.did().is_local() && adt.is_struct()=>{
            for f in adt.all_fields(){type_ok(tcx,f.ty(tcx,args),template,depth+1)?;}Ok(())
        },
        ty::Closure(def,args) if def.is_local()=>{
            for t in args.as_closure().upvar_tys().iter(){type_ok(tcx,t,template,depth+1)?;}Ok(())
        },
        ty::FnDef(_,_)=>Ok(()),
        _=>Err(format!("unsupported type: {t:?}"))
    }
}
fn place(p:mir::Place<'_>)->R<Value>{
    let mut projections=Vec::new();
    for element in p.projection.iter(){
        projections.push(match element {
            mir::ProjectionElem::Deref=>json!({"kind":"deref"}),
            mir::ProjectionElem::Field(index,ty)=>json!({"kind":"field","index":index.as_usize(),"type":format!("{ty:?}")}),
            _=>return Err(format!("unsupported place projection: {element:?}"))
        });
    }
    Ok(json!({"local":p.local.as_usize(),"projection":projections}))
}
struct BodyCapture<'tcx>{tcx:TyCtxt<'tcx>, template:bool, dependencies:Vec<(String,Instance<'tcx>)>}
impl<'tcx> BodyCapture<'tcx>{
    fn resolve(&mut self,kind:&str,def:DefId,args:ty::GenericArgsRef<'tcx>)->R<String>{
        let instance=Instance::try_resolve(self.tcx,TypingEnv::fully_monomorphized(),def,args)
            .map_err(|_|"compiler instance-resolution error".to_string())?
            .ok_or_else(||format!("unresolved instance: {} {args:?}",self.tcx.def_path_str(def)))?;
        let id=instance_id(self.tcx,instance);self.dependencies.push((kind.into(),instance));Ok(id)
    }
    fn operand(&mut self,o:&mir::Operand<'tcx>)->R<Value>{
        match o {
            mir::Operand::Copy(p)=>Ok(json!({"kind":"copy","place":place(*p)?})),
            mir::Operand::Move(p)=>Ok(json!({"kind":"move","place":place(*p)?})),
            mir::Operand::Constant(c)=>{
                let t=c.const_.ty();
                if let ty::FnDef(def,args)=t.kind(){return Ok(json!({"kind":"function","definition":self.tcx.def_path_str(*def),"arguments":format!("{args:?}")}));}
                type_ok(self.tcx,t,self.template,0)?;let mut dependency=None;
                if let mir::Const::Unevaluated(u,_)=c.const_ {
                    if u.promoted.is_some(){return Err("promoted constant unsupported".into());}
                    if !self.template {dependency=Some(self.resolve("constant",u.def,u.args)?);}
                }
                let bits=if self.template {None} else {c.const_.try_eval_bits(self.tcx,TypingEnv::fully_monomorphized()).map(|n|n.to_string())};
                if !self.template && bits.is_none() && !t.is_unit(){return Err(format!("non-scalar/unresolved constant: {:?}",c.const_));}
                Ok(json!({"kind":"constant","type":format!("{t:?}"),"compiler_value":format!("{:?}",c.const_),"evaluated_bits":bits,"dependency":dependency}))
            },
            _=>Err(format!("unsupported operand: {o:?}"))
        }
    }
    fn rvalue(&mut self,r:&mir::Rvalue<'tcx>)->R<Value>{
        Ok(match r {
            mir::Rvalue::Use(o)=>json!({"kind":"use","operand":self.operand(o)?}),
            mir::Rvalue::Ref(region,kind,p)=>json!({"kind":"reference","region":format!("{region:?}"),"borrow_kind":format!("{kind:?}"),"place":place(*p)?}),
            mir::Rvalue::RawPtr(kind,p)=>json!({"kind":"raw_address","pointer_kind":format!("{kind:?}"),"place":place(*p)?}),
            mir::Rvalue::BinaryOp(op,pair)=>{
                if !matches!(op,mir::BinOp::BitXor|mir::BinOp::BitAnd|mir::BinOp::BitOr|mir::BinOp::Eq|mir::BinOp::Ne){return Err(format!("unsupported binary operation {op:?}"));}
                json!({"kind":"binary","operator":format!("{op:?}"),"left":self.operand(&pair.0)?,"right":self.operand(&pair.1)?})
            },
            mir::Rvalue::UnaryOp(op,o)=>{
                if !matches!(op,mir::UnOp::Not){return Err(format!("unsupported unary operation {op:?}"));}
                json!({"kind":"unary","operator":format!("{op:?}"),"operand":self.operand(o)?})
            },
            mir::Rvalue::Aggregate(kind,ops)=>{
                let mut dependency=None;
                match &**kind {
                    mir::AggregateKind::Tuple=>{},
                    mir::AggregateKind::Adt(def,_,_,_,_) if def.is_local() && self.tcx.adt_def(*def).is_struct()=>{},
                    mir::AggregateKind::Closure(def,args) if def.is_local()=>{
                        if !self.template {dependency=Some(self.resolve("closure-construction",*def,args)?);}
                    },
                    _=>return Err(format!("unsupported aggregate {kind:?}"))
                }
                let values:Vec<_>=ops.iter().map(|o|self.operand(o)).collect::<R<_>>()?;
                json!({"kind":"aggregate","aggregate_kind":format!("{kind:?}"),"operands":values,"closure_dependency":dependency})
            },
            mir::Rvalue::Cast(mir::CastKind::IntToInt,o,t)=>json!({"kind":"integer_cast","operand":self.operand(o)?,"target_type":format!("{t:?}")}),
            mir::Rvalue::CopyForDeref(p)=>json!({"kind":"copy_for_deref","place":place(*p)?}),
            _=>return Err(format!("unsupported rvalue {r:?}"))
        })
    }
    fn body(&mut self,b:&mir::Body<'tcx>)->R<Value>{
        if b.coroutine.is_some() || b.tainted_by_errors.is_some() || b.basic_blocks.len()>128 || b.local_decls.len()>128 {return Err("coroutine, compiler-tainted or body bound unsupported".into());}
        let mut locals=Vec::new();
        for (id,d) in b.local_decls.iter_enumerated(){
            type_ok(self.tcx,d.ty,self.template,0)?;
            let layout=if self.template {None} else {
                let l=self.tcx.layout_of(TypingEnv::fully_monomorphized().as_query_input(d.ty)).map_err(|_|format!("unsupported layout {:?}",d.ty))?;
                Some(json!({"size_bytes":l.size.bytes(),"align_bytes":l.align.abi.bytes(),"backend_representation":format!("{:?}",l.backend_repr)}))
            };
            locals.push(json!({"id":id.as_usize(),"type":format!("{:?}",d.ty),"mutability":format!("{:?}",d.mutability),"layout":layout}));
        }
        let mut blocks=Vec::new();
        for (id,bb) in b.basic_blocks.iter_enumerated(){
            if bb.statements.len()>512{return Err("statement bound exceeded".into());}
            let mut statements=Vec::new();
            for s in &bb.statements {
                let value=match &s.kind {
                    mir::StatementKind::Assign(pair)=>json!({"kind":"assign","destination":place(pair.0)?,"value":self.rvalue(&pair.1)?}),
                    mir::StatementKind::StorageLive(l)=>json!({"kind":"storage_live","local":l.as_usize()}),
                    mir::StatementKind::StorageDead(l)=>json!({"kind":"storage_dead","local":l.as_usize()}),
                    mir::StatementKind::Nop=>json!({"kind":"nop"}),
                    _=>return Err(format!("unsupported statement {:?}",s.kind))
                };statements.push(json!({"operation":value,"origin":origin(self.tcx,s.source_info.span)}));
            }
            let t=bb.terminator.as_ref().ok_or("missing terminator")?;
            let term=match &t.kind {
                mir::TerminatorKind::Return=>json!({"kind":"return"}),
                mir::TerminatorKind::Goto{target}=>json!({"kind":"goto","target":target.as_usize()}),
                mir::TerminatorKind::SwitchInt{discr,targets}=>json!({"kind":"switch","operand":self.operand(discr)?,"cases":targets.iter().map(|(v,t)|json!({"value":v.to_string(),"target":t.as_usize()})).collect::<Vec<_>>(),"otherwise":targets.otherwise().as_usize()}),
                mir::TerminatorKind::Unreachable=>json!({"kind":"unreachable"}),
                mir::TerminatorKind::UnwindResume=>json!({"kind":"unwind_resume"}),
                mir::TerminatorKind::UnwindTerminate(reason)=>json!({"kind":"unwind_terminate","reason":format!("{reason:?}")}),
                mir::TerminatorKind::Call{func,args,destination,target,unwind,..}=>{
                    let ty=func.ty(&b.local_decls,self.tcx);
                    let ty::FnDef(def,generic_args)=ty.kind() else{return Err("indirect/dynamic/function-pointer call unsupported".into());};
                    let resolved=if self.template {None} else {Some(self.resolve("call",*def,generic_args)?)};
                    json!({"kind":"call","function":self.operand(func)?,"resolved_instance":resolved,"arguments":args.iter().map(|a|self.operand(&a.node)).collect::<R<Vec<_>>>()?,"destination":place(*destination)?,"target":target.map(|x|x.as_usize()),"unwind":format!("{unwind:?}")})
                },
                mir::TerminatorKind::Drop{place:p,target,unwind,replace,drop,async_fut}=>{
                    if async_fut.is_some(){return Err("async drop unsupported".into());}
                    let ty=p.ty(&b.local_decls,self.tcx).ty;
                    let resolved=if self.template {None} else {
                        let i=Instance::resolve_drop_in_place(self.tcx,ty);
                        let key=instance_id(self.tcx,i);self.dependencies.push(("drop".into(),i));Some(key)
                    };
                    json!({"kind":"drop","place":place(*p)?,"type":format!("{ty:?}"),"resolved_instance":resolved,"target":target.as_usize(),"unwind":format!("{unwind:?}"),"replace":replace,"drop_block":drop.map(|x|x.as_usize())})
                },
                _=>return Err(format!("unsupported terminator {:?}",t.kind))
            };
            blocks.push(json!({"id":id.as_usize(),"cleanup":bb.is_cleanup,"statements":statements,"terminator":term,"origin":origin(self.tcx,t.source_info.span)}));
        }
        let required=if let Some(constants)=&b.required_consts {constants.iter().map(|c|self.operand(&mir::Operand::Constant(Box::new(c.clone())))).collect::<R<Vec<_>>>()?}else{Vec::new()};
        Ok(json!({"argument_count":b.arg_count,"spread_argument":b.spread_arg.map(|l|l.as_usize()),"is_polymorphic":b.is_polymorphic,"phase":format!("{:?}",b.phase),"locals":locals,"blocks":blocks,"required_constants":required,"origin":origin(self.tcx,b.span)}))
    }
}

fn capture<'tcx>(tcx:TyCtxt<'tcx>,requested:&str)->R<Value>{
    let body_ids:Vec<_>=tcx.hir_body_owners().collect();
    let roots:Vec<_>=body_ids.iter().filter(|id|tcx.def_path_str(id.to_def_id())==requested).copied().collect();
    if roots.len()!=1{return Err("requested root is absent or ambiguous".into());}
    let root=roots[0].to_def_id();
    if tcx.def_kind(root)!=DefKind::Fn || tcx.generics_of(root).count()!=0 {return Err("root must be a nongeneric local function".into());}
    let mut queue=VecDeque::from([Instance::mono(tcx,root)]);let mut bodies=BTreeMap::new();let mut edges=BTreeSet::new();
    while let Some(instance)=queue.pop_front(){
        let key=instance_id(tcx,instance);if bodies.contains_key(&key){continue;}
        if bodies.len()>=64{return Err("instance closure exceeds 64".into());}
        match instance.def {
            InstanceKind::Item(def) if def.is_local()=>{},
            InstanceKind::DropGlue(_,_)|InstanceKind::ClosureOnceShim{..}=>{},
            _=>return Err(format!("unsupported external/intrinsic/virtual/shim instance {key}"))
        }
        let raw=tcx.instance_mir(instance.def);
        let normalized=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,TypingEnv::fully_monomorphized(),EarlyBinder::bind(raw.clone())).map_err(|_|format!("MIR normalization failed: {key}"))?;
        let mut c=BodyCapture {tcx,template:false,dependencies:Vec::new()};let body=c.body(&normalized)?;
        for (kind,dependency) in c.dependencies {
            edges.insert((key.clone(),kind,instance_id(tcx,dependency)));queue.push_back(dependency);
        }
        bodies.insert(key.clone(),json!({"id":key,"definition":tcx.def_path_str(instance.def_id()),"kind":format!("{:?}",instance.def),"arguments":format!("{:?}",instance.args),"query_origin":"TyCtxt::instance_mir + try_instantiate_mir_and_normalize_erasing_regions","body":body}));
    }
    let mut templates=Vec::new();
    for id in body_ids {
        let def=id.to_def_id();let mut c=BodyCapture {tcx,template:true,dependencies:Vec::new()};
        let body=c.body(tcx.instance_mir(InstanceKind::Item(def)))?;
        templates.push(json!({"definition":tcx.def_path_str(def),"kind":format!("{:?}",tcx.def_kind(def)),"query_origin":"TyCtxt::instance_mir (uninstantiated local body)","body":body}));
    }
    templates.sort_by_key(|v|v["definition"].as_str().unwrap_or_default().to_owned());
    let mut definitions=Vec::new();
    for id in tcx.iter_local_def_id(){
        let kind=tcx.def_kind(id);
        if matches!(kind,DefKind::ForeignMod|DefKind::GlobalAsm|DefKind::SyntheticCoroutineBody|DefKind::OpaqueTy){return Err(format!("unsupported local owner kind {kind:?}"));}
        definitions.push(json!({"id":format!("{id:?}"),"path":tcx.def_path_str(id.to_def_id()),"kind":format!("{kind:?}"),"parent":format!("{:?}",tcx.opt_parent(id.to_def_id())),"origin":origin(tcx,tcx.def_span(id)),"hir":format!("{:?}",tcx.hir_node_by_def_id(id))}));
    }
    let mut sources=Vec::new();
    for file in tcx.sess.source_map().files().iter(){if !file.is_imported(){if let Some(text)=&file.src {sources.push(json!({"name":file.name.prefer_remapped_unconditionally().to_string(),"compiler_source":text.to_string()}));}}}
    sources.sort_by_key(|v|v["name"].as_str().unwrap_or_default().to_owned());
    let mut cfg:Vec<_>=tcx.sess.config.iter().map(|v|format!("{v:?}")).collect();cfg.sort();
    let mut features:Vec<_>=tcx.features().enabled_features().iter().map(|x|x.to_string()).collect();features.sort();
    if !features.is_empty(){return Err("unstable language/library features are outside this capture domain".into());}
    let mut file_inputs:Vec<_>=tcx.sess.file_depinfo.lock().iter().map(|x|x.to_string()).collect();file_inputs.sort();
    let mut environment_inputs:Vec<_>=tcx.sess.env_depinfo.lock().iter().map(|x|format!("{x:?}")).collect();environment_inputs.sort();
    let dependencies:Vec<_>=tcx.crates(()).iter().map(|id|json!({"name":tcx.crate_name(*id).to_string(),"crate_hash":format!("{:?}",tcx.crate_hash(*id))})).collect();
    Ok(json!({"schema":"owned-configured-capture-v1","root":tcx.def_path_str(root),"crate_name":tcx.crate_name(LOCAL_CRATE).to_string(),"effective_cfg":cfg,"language_features":features,"target":format!("{:#?}",tcx.sess.target),"codegen_target_cpu":format!("{:?}",tcx.sess.opts.cg.target_cpu),"codegen_target_features":format!("{:?}",tcx.sess.opts.cg.target_feature),"additional_file_inputs":file_inputs,"environment_inputs":environment_inputs,"sources":sources,"local_definitions":definitions,"local_body_templates":templates,"instances":bodies.into_values().collect::<Vec<_>>(),"edges":edges.into_iter().map(|(from,kind,to)|json!({"from":from,"kind":kind,"to":to})).collect::<Vec<_>>(),"external_crate_metadata":dependencies,"trust_frontier":"rustc parser/analysis/expansion/CTFE/resolution/MIR and this observer; no Rust safety theorem"}))
}
struct Observer {root:String,result:Option<R<Value>>}
impl Callbacks for Observer {
    fn after_analysis<'tcx>(&mut self,_compiler:&interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation{self.result=Some(capture(tcx,&self.root));Compilation::Stop}
}
fn run()->std::process::ExitCode{
    let args:Vec<String>=std::env::args().collect();
    if args.len()<5 || args[3]!="--" {eprintln!("usage: observer ROOT FRESH_OUTPUT -- RUSTC_ARGS...");return std::process::ExitCode::from(64);}
    let mut rustc_args=vec![args[0].clone()];rustc_args.extend_from_slice(&args[4..]);
    let mut observer=Observer {root:args[1].clone(),result:None};rustc_driver::run_compiler(&rustc_args,&mut observer);
    let (result,status)=match observer.result {
        Some(Ok(v))=>(v,0),
        Some(Err(reason))=>(json!({"schema":"owned-capture-rejection-v1","status":"unsupported","reason":reason}),65),
        None=>(json!({"status":"operational-failure","reason":"normal analysis callback not reached"}),70)
    };
    let output=std::fs::OpenOptions::new().write(true).create_new(true).open(&args[2]);
    let written=output.and_then(|mut f|{let bytes=serde_json::to_vec_pretty(&result)?;f.write_all(&bytes)});
    if let Err(error)=written {eprintln!("owned output error: {error}");return std::process::ExitCode::from(74);}
    std::process::ExitCode::from(status)
}
fn main()->std::process::ExitCode{rustc_driver::catch_with_exit_code(run)}
