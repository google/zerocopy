# CAP 1.2 conformance probe for the archived Google CAP library

Support material for the report in the parent directory. All files are plain text,
and every alert message is synthetic.

## Files

- `make_cases.py <out dir>`: writes 29 CAP 1.2 alerts (`c01`–`c29`). Each differs from a
  minimal valid baseline in one respect. It also writes `cases.tsv`, which records the
  expectation each case derives from the CAP 1.2 text.
- `CapProbe.java`: parses every case with `new CapXmlParser(false).parseFrom(xml, reasons)`
  (extended XSD plus the core `CapValidator`). It records reasons or exceptions, then
  applies `Ipaws1Profile` and `GoogleProfile` when an alert object was produced. It also
  times the warm `parseFrom` path on the baseline.
- `results/probe_out.txt`: output of the run reported in `REPORT.md`.
- `results/cases.tsv`: expectations per case.

## Reproduce

The library at the pinned revision needs Java 8: it uses `javax.xml.bind` and an internal
Xerces class.

```sh
git clone https://github.com/google/cap-library && git -C cap-library checkout 67dcf20373834725b15c5325a73f615d92a708fa
CP=$(ls cap-library/java/lib/*.jar | tr '\n' ':')
mkdir -p classes && javac -cp "$CP" -d classes $(find cap-library/java/src -name '*.java')
mkdir -p classes/com/google/publicalerts/cap/schema && cp -r cap-library/schema/* classes/com/google/publicalerts/cap/schema/
(cd cap-library/java/src && find . -type f ! -name '*.java' -exec cp --parents {} ../../../classes/ \;)
python3 make_cases.py /tmp/cases
javac -cp "classes:$CP" -d probe CapProbe.java
java -cp "probe:classes:$CP" CapProbe /tmp/cases
```

The reported run used the `eclipse-temurin:8u432-b06-jdk` container (OpenJDK 1.8.0_432)
with networking disabled.
