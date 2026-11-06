import sys, os, json, hashlib, io, unittest, platform
from pathlib import Path
sys.dont_write_bytecode = True
scratch = Path(__file__).resolve().parent
(scratch / 'tmp').mkdir(exist_ok=True)
os.environ['TMPDIR'] = str(scratch / 'tmp')
source = Path(sys.argv[1]).resolve()
if not (source / 'tests/test_admission.py').is_file():
 raise SystemExit('Expected pinned verification/aeneas source directory')
sys.path.insert(0, str(source / 'tests'))
import test_admission, test_trait_invariants
selection = {
 'test_admission.AdmissionTests': [
  'test_abstract_dispatch_is_an_exact_declared_generic_input',
  'test_trait_impl_methods_remain_executable_admission_roots',
  'test_missing_registration_is_not_an_opaque_success',
  'test_drop_before_cleanup_and_on_unwind_is_rejected',
  'test_new_operations_attributes_and_configuration_fail_closed',
  'test_ub_abort_must_not_become_unwind_termination'],
 'test_trait_invariants.TraitBindingsTests': [
  'test_native_mapping_requires_complete_exact_dictionary_identity',
  'test_every_local_impl_requires_binding_and_proof_selection',
  'test_array_impl_retains_usize_const_and_original_application',
  'test_const_expressions_and_non_usize_lengths_fail_closed']}
stream=io.StringIO(); suite=unittest.TestSuite()
for cls, names in selection.items():
 for name in names: suite.addTest(unittest.defaultTestLoader.loadTestsFromName(cls+'.'+name))
result=unittest.TextTestRunner(stream=stream, verbosity=2, failfast=True).run(suite)
identities=[]
for name,module in list(sys.modules.items()):
 path=getattr(module, '__file__', None)
 if path and Path(path).is_relative_to(source):
  path=Path(path); identities.append({'module':name,'path':str(path.relative_to(source)), 'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
(scratch/'admission-control-results.json').write_text(json.dumps({'command':[sys.executable,'-B',str(Path(__file__).resolve()),str(source)],'source_directory':str(source),'selection':selection,'python':sys.version,'executable':sys.executable,'platform':platform.platform(),'tests_run':result.testsRun,'successful':result.wasSuccessful(),'output':stream.getvalue(),'source_files':identities},indent=2)+'\n')
print(stream.getvalue()); sys.exit(0 if result.wasSuccessful() else 1)
