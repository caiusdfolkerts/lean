"""Diagnostic-only unchanged source build, with expanded bounded error evidence."""
from pathlib import Path
import sys,json,hashlib,os,datetime
pipeline=Path(sys.argv[1]).resolve();sys.path.insert(0,str(pipeline))
from scripts import verify_submission as v
assert v.MAX_BUILD_ERROR_EXCERPTS==20 and v.MAX_BUILD_ERROR_EXCERPT_CHARS==8000
# Change only the number of retained error excerpts; no verifier or source file is modified.
v.MAX_BUILD_ERROR_EXCERPTS=100
output=Path(os.environ['RUNNER_TEMP'])/'mechanical-report.json'
args=v.parser().parse_args(['execute','--work-dir',str(Path(os.environ['RUNNER_TEMP'])/'palomar'),'--output',str(output),'--bwrap',os.environ['PALOMAR_BWRAP'],'--bwrap-source-tag','v0.12.0','--workflow-url',os.environ['DIAGNOSTIC_WORKFLOW_URL'],'--execution-budget-seconds','19800'])
rc=1
try:
 rc=args.func(args)
finally:
 report=json.loads(output.read_text()) if output.exists() else {}
 errors=report.get('build_error_excerpts',{})
 receipt={'kind':'diagnostic-only exact original source error collection; never an official full pass','original_source_commit':'4e3c0d23cbd0b59b1c69a90644536cc268a0c932','diagnostic_commit':os.environ['GITHUB_SHA'],'workflow_run':os.environ['GITHUB_RUN_ID'],'pipeline_commit':'14aa8d6b3c2f14a8540605e37144560b9a00e7e7','pipeline_source_file_sha256':hashlib.sha256(Path(v.__file__).read_bytes()).hexdigest(),'report_capture_only_change':{'MAX_BUILD_ERROR_EXCERPTS':{'original':20,'diagnostic':100}},'unchanged_excerpt_chars':8000,'maximum_error_excerpt_bytes':800000,'expected_prior_errors':53,'reported_errors':len(errors.get('errors',[])),'omitted_error_count':errors.get('omitted_error_count'),'output_truncated':errors.get('output_truncated'),'per_error_truncation_count':sum(bool(x.get('truncated')) for x in errors.get('errors',[])),'exact_source':report.get('source'),'stage':report.get('stage'),'status':report.get('status'),'execute_exit_code':rc,'mechanical_report_sha256':hashlib.sha256(output.read_bytes()).hexdigest() if output.exists() else None,'no_full_preflight_pass_claim':True}
 (Path(os.environ['RUNNER_TEMP'])/'source-error-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('SOURCE_ERROR_COLLECTION_SUMMARY '+json.dumps(receipt))
raise SystemExit(rc)
