# Observation regex review (no producer launched)

The only predicate edit removes one extra literal closing parenthesis after `digest_bytes.(i)`. Original source, generated artifact, reviewed ML entries and producer driver are unchanged.

Old full pattern:

```text
\(\* update digest \*\)\nloaded_files := \n  let digest_bytes = \[\|([0-9; ]+)\|\] in\n  let digest = Bytes.init \(Array.length digest_bytes\) \(fun i -> Char.chr digest_bytes.\(i\)\)\) in\n  \("([^"]+)", Bytes.to_string digest\)::!loaded_files;;
```

Proposed full pattern:

```text
\(\* update digest \*\)\nloaded_files := \n  let digest_bytes = \[\|([0-9; ]+)\|\] in\n  let digest = Bytes.init \(Array.length digest_bytes\) \(fun i -> Char.chr digest_bytes.\(i\)\) in\n  \("([^"]+)", Bytes.to_string digest\)::!loaded_files;;
```

Exact first actual generated digest record:

```ocaml
(* update digest *)
loaded_files := 
  let digest_bytes = [|227; 197; 144; 225; 227; 254; 31; 204; 25; 133; 146; 234; 33; 8; 226; 83|] in
  let digest = Bytes.init (Array.length digest_bytes) (fun i -> Char.chr digest_bytes.(i)) in
  ("system.ml", Bytes.to_string digest)::!loaded_files;;
```

Data-only regression:

```json
{
  "artifact_sha256": "311e298d5303ee4a0d352b87301839a7b6f0438674d140b677fd9cba8dbce0a7",
  "initial_matches": 0,
  "corrected_matches": 47,
  "raw_digest_markers": 47,
  "exact_reverse_completion_prediction": true,
  "producer_spec_exists": false,
  "producer_log_exists": false,
  "scope": "Data-only regex regression on unchanged actual copied inliner text; no source path traversal or runtime/build"
}
```

Producer effects: none. `specs/producer.json` has never been created. The first gate stopped its Python preparation before spec creation. A dependent host call attempted to read that absent spec and failed before Popen/Docker. During local regression, invoking the full runtime-path census function on the host also failed because `/home/opam/...` does not exist there; its dependent corrected-census spec was likewise never created and the attempted host wrapper failed before Popen/Docker. Neither error ran a producer, proof or container command. This regression directly parses the saved artifact text and avoids the invalid host path lookup.
