// PREPARATION ONLY: proposed E33 observer, not compiled or run.
// rustc-private API spellings below were checked against f53b654a compiler source,
// not against a successful build. This observer is NOT the final input acceptor.
// Only independently fixed, validated consumer selectors may reach this program.
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;
extern crate serde_json;
use rustc_abi::{BackendRepr, Primitive, Reg, Scalar};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::ty::{self, Instance, Ty, TyCtxt, TypingEnv};
use rustc_span::def_id::LOCAL_CRATE;
use rustc_target::callconv::{ArgAbi, ArgAttributes, FnAbi, PassMode};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::io::Write;
type R<T> = Result<T, String>;

fn primitive(p: Primitive) -> Value {
    match p {
        Primitive::Int(i, signed) => json!({"kind":"integer","integer":format!("{i:?}"),"signed":signed}),
        Primitive::Float(f) => json!({"kind":"float","float":format!("{f:?}")}),
        Primitive::Pointer(a) => json!({"kind":"pointer","address_space":format!("{a:?}")}),
    }
}
fn scalar(s: Scalar) -> Value {
    match s {
        Scalar::Initialized { value, valid_range } => json!({"kind":"initialized","primitive":primitive(value),"valid_range_start":valid_range.start.to_string(),"valid_range_end":valid_range.end.to_string()}),
        Scalar::Union { value } => json!({"kind":"union","primitive":primitive(value),"valid_range":null}),
    }
}
fn repr(r: BackendRepr) -> R<Value> {
    Ok(match r {
        BackendRepr::Scalar(s) => json!({"kind":"scalar","scalar":scalar(s)}),
        BackendRepr::ScalarPair(a,b) => json!({"kind":"scalar_pair","first":scalar(a),"second":scalar(b)}),
        BackendRepr::SimdVector { element,count } => json!({"kind":"simd_vector","element":scalar(element),"count":count}),
        BackendRepr::Memory { sized } => json!({"kind":"memory","sized":sized}),
        BackendRepr::SimdScalableVector { .. } => return Err("scalable vector outside fixed E33 selection".into()),
    })
}
fn attrs(a: &ArgAttributes) -> Value {
    json!({"regular_bits":a.regular.bits(),"regular_debug":format!("{:?}",a.regular),"extension":format!("{:?}",a.arg_ext),"pointee_size_bytes":a.pointee_size.bytes(),"pointee_align_bytes":a.pointee_align.map(|x|x.bytes())})
}
fn reg(r: Reg) -> Value {json!({"kind":format!("{:?}",r.kind),"size_bytes":r.size.bytes()})}
fn argument(a: &ArgAbi<'_, Ty<'_>>) -> R<Value> {
    let l=a.layout;
    let count=l.fields.count();
    if count>64 {return Err("top-level field count exceeds 64".into());}
    let offsets:Vec<_>=(0..count).map(|i|l.fields.offset(i).bytes()).collect();
    let mode=match &a.mode {
        PassMode::Ignore => json!({"kind":"ignore"}),
        PassMode::Direct(x) => json!({"kind":"direct","attrs":attrs(x)}),
        PassMode::Pair(a,b) => json!({"kind":"pair","first":attrs(a),"second":attrs(b)}),
        PassMode::Cast { pad_i32, cast } => json!({"kind":"cast","pad_i32":pad_i32,"prefix":cast.prefix.iter().map(|x|x.map(reg)).collect::<Vec<_>>(),"rest_offset_bytes":cast.rest_offset.map(|x|x.bytes()),"rest_unit":reg(cast.rest.unit),"rest_total_bytes":cast.rest.total.bytes(),"rest_is_consecutive":cast.rest.is_consecutive,"attrs":attrs(&cast.attrs)}),
        PassMode::Indirect { attrs:a,meta_attrs,on_stack } => json!({"kind":"indirect","attrs":attrs(a),"meta_attrs":meta_attrs.as_ref().map(attrs),"on_stack":on_stack}),
    };
    Ok(json!({"type":format!("{}",l.ty),"type_debug":format!("{:?}",l.ty),"layout":{"size_bytes":l.size.bytes(),"abi_align_bytes":l.align.abi.bytes(),"unadjusted_abi_align_bytes":l.unadjusted_abi_align.bytes(),"max_repr_align_bytes":l.max_repr_align.map(|x|x.bytes()),"uninhabited":l.uninhabited,"backend_repr":repr(l.backend_repr)?,"field_offsets_bytes":offsets,"fields_debug":format!("{:?}",l.fields),"variants_debug":format!("{:?}",l.variants),"largest_niche_debug":format!("{:?}",l.largest_niche),"full_layout_debug":format!("{:?}",l.layout)},"mode":mode}))
}
fn fn_abi(a:&FnAbi<'_,Ty<'_>>) -> R<Value> {
    let args=a.args.iter().map(argument).collect::<R<Vec<_>>>()?;
    Ok(json!({"args":args,"ret":argument(&a.ret)?,"c_variadic":a.c_variadic,"fixed_count":a.fixed_count,"canonical_convention":format!("{:?}",a.conv),"can_unwind":a.can_unwind}))
}
fn parse_ty<'tcx>(tcx:TyCtxt<'tcx>, s:&str)->R<Ty<'tcx>> {
    Ok(match s {"u8"=>tcx.types.u8,"u32"=>tcx.types.u32,"u64"=>tcx.types.u64,"i32"=>tcx.types.i32,"f64"=>tcx.types.f64,"*const u8"=>Ty::new_imm_ptr(tcx,tcx.types.u8),_=>return Err(format!("type selector outside finite table: {s}"))})
}
fn string<'a>(v:&'a Value,key:&str)->R<&'a str>{v[key].as_str().ok_or_else(||format!("missing string {key}"))}
fn list<'a>(v:&'a Value,key:&str)->R<&'a Vec<Value>>{v[key].as_array().ok_or_else(||format!("missing array {key}"))}
fn keys(v:&Value,expected:&[&str])->R<()> {
    let m=v.as_object().ok_or("object required")?;
    if m.len()!=expected.len()||expected.iter().any(|k|!m.contains_key(*k)){return Err("unknown or missing selector field".into());}Ok(())
}
fn capture(tcx:TyCtxt<'_>, request:&Value)->R<Value> {
    keys(request,&["schema","selections"])?;
    if string(request,"schema")? != "e33-proposed-selectors-v1" {return Err("selector schema".into());}
    let sels=list(request,"selections")?;
    if sels.is_empty()||sels.len()>32 {return Err("need 1..32 selections".into());}
    let defs:Vec<_>=tcx.iter_local_def_id().collect();
    let typing=TypingEnv::fully_monomorphized();let mut selected=Vec::new();let mut seen=BTreeSet::new();
    for s in sels {
        keys(s,&["path","query","type_args","extra_args"])?;
        let path=string(s,"path")?;let query=string(s,"query")?;
        if !seen.insert(serde_json::to_string(s).map_err(|e|e.to_string())?){return Err("duplicate selection".into());}
        let hits:Vec<_>=defs.iter().filter(|d|tcx.def_path_str(d.to_def_id())==path).copied().collect();
        if hits.len()!=1 {return Err(format!("selected definition absent/ambiguous: {path}"));}
        let def=hits[0].to_def_id();
        let ts=list(s,"type_args")?.iter().map(|x|x.as_str().ok_or("type argument string required").map_err(String::from).and_then(|x|parse_ty(tcx,x))).collect::<R<Vec<_>>>()?;
        let es=list(s,"extra_args")?.iter().map(|x|x.as_str().ok_or("extra argument string required").map_err(String::from).and_then(|x|parse_ty(tcx,x))).collect::<R<Vec<_>>>()?;
        let extra=tcx.mk_type_list(&es);
        let (identity,result)=match query {
            "instance"=>{
                if tcx.def_kind(def)!=DefKind::Fn || !es.is_empty(){return Err("only local ordinary Fn instances with no variadic extras".into());}
                let gs=tcx.generics_of(def);
                if gs.parent.is_some()||gs.parent_count!=0||gs.count()!=ts.len()||gs.own_params.iter().any(|p|!matches!(p.kind,ty::GenericParamDefKind::Type{..})){return Err("instance generic arguments not in finite type-only selector domain".into());}
                let args=tcx.mk_args_from_iter(ts.iter().copied().map(ty::GenericArg::from));
                let i=Instance::try_resolve(tcx,typing,def,args).map_err(|_|"instance resolution error")?.ok_or("unresolved instance")?;
                if !matches!(i.def,ty::InstanceKind::Item(d) if d.is_local()){return Err("nonlocal/virtual/shim instance outside selection".into());}
                let a=tcx.fn_abi_of_instance(typing.as_query_input((i,extra))).map_err(|e|format!("FnAbi query error: {e:?}"))?;
                (json!({"instance_kind":format!("{:?}",i.def),"arguments_debug":format!("{:?}",i.args),"declared_signature_debug":format!("{:?}",tcx.fn_sig(def).instantiate(tcx,i.args))}),fn_abi(a)?)
            },
            "fn_ptr"=>{
                if tcx.def_kind(def)!=DefKind::TyAlias || !ts.is_empty() || tcx.generics_of(def).count()!=0{return Err("nongeneric function-pointer alias required".into());}
                let t=tcx.type_of(def).instantiate_identity().skip_norm_wip();
                let ty::FnPtr(sig_tys,hdr)=t.kind() else {return Err("alias is not FnPtr".into())};
                let sig=sig_tys.with(*hdr);
                if !sig.skip_binder().c_variadic()&&!es.is_empty(){return Err("extras on nonvariadic signature rejected before compiler query".into());}
                let a=tcx.fn_abi_of_fn_ptr(typing.as_query_input((sig,extra))).map_err(|e|format!("FnAbi pointer query error: {e:?}"))?;
                (json!({"function_pointer_type":format!("{t:?}")}),fn_abi(a)?)
            },
            _=>return Err("unknown query selector".into()),
        };
        selected.push(json!({"selection":s,"resolved_definition":tcx.def_path_str(def),"definition_kind":format!("{:?}",tcx.def_kind(def)),"identity":identity,"fn_abi":result}));
    }
    let mut sources=Vec::new();
    for f in tcx.sess.source_map().files().iter(){if !f.is_imported(){if let Some(text)=&f.src {sources.push(json!({"name":f.name.prefer_remapped_unconditionally().to_string(),"compiler_source":text.to_string()}));}}}
    sources.sort_by_key(|v|v["name"].as_str().unwrap_or_default().to_owned());
    let mut cfg:Vec<_>=tcx.sess.config.iter().map(|x|format!("{x:?}")).collect();cfg.sort();
    let deps:Vec<_>=tcx.crates(()).iter().map(|id|json!({"crate":tcx.crate_name(*id).to_string(),"crate_hash":format!("{:?}",tcx.crate_hash(*id))})).collect();
    Ok(json!({"schema":"e33-proposed-observation-v1","crate_name":tcx.crate_name(LOCAL_CRATE).to_string(),"target_spec_debug":format!("{:#?}",tcx.sess.target),"target_triple_debug":format!("{:?}",tcx.sess.opts.target_triple),"target_cpu":format!("{:?}",tcx.sess.opts.cg.target_cpu),"target_features":tcx.sess.opts.cg.target_feature,"opt_level":format!("{:?}",tcx.sess.opts.optimize),"incremental_enabled":tcx.sess.opts.incremental.is_some(),"effective_cfg":cfg,"source_files":sources,"external_crates":deps,"selected":selected,"trust_frontier":"Pinned rustc analysis/layout/FnAbi, this unvalidated observer and future caller-bound comparison; no source safety or physical placement theorem"}))
}
struct Observer {request:Value,result:Option<R<Value>>}
impl Callbacks for Observer {
    fn after_analysis<'tcx>(&mut self,_:&interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {self.result=Some(capture(tcx,&self.request));Compilation::Stop}
}
fn run()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    if args.len()<5||args[3]!="--" {eprintln!("usage: observer LOCKED_SELECTORS FRESH_OUTPUT -- RUSTC_ARGS...");return std::process::ExitCode::from(64);}
    let request:Value=match std::fs::read(&args[1]).map_err(|e|e.to_string()).and_then(|b|serde_json::from_slice(&b).map_err(|e|e.to_string())){Ok(v)=>v,Err(e)=>{eprintln!("selector read failure: {e}");return std::process::ExitCode::from(64)}};
    let mut cb=Observer {request,result:None};let mut compiler_args=vec![args[0].clone()];compiler_args.extend_from_slice(&args[4..]);
    rustc_driver::run_compiler(&compiler_args,&mut cb);
    let (value,status)=match cb.result {Some(Ok(v))=>(v,0),Some(Err(s))=>(json!({"status":"outside-observer-domain","reason":s}),65),None=>(json!({"status":"operational-failure","reason":"analysis callback absent"}),70)};
    let written=std::fs::OpenOptions::new().create_new(true).write(true).open(&args[2]).and_then(|mut f|{let b=serde_json::to_vec_pretty(&value)?;f.write_all(&b)});
    if let Err(e)=written {eprintln!("fresh output failure: {e}");return std::process::ExitCode::from(74);}
    std::process::ExitCode::from(status)
}
fn main()->std::process::ExitCode {rustc_driver::catch_with_exit_code(run)}
