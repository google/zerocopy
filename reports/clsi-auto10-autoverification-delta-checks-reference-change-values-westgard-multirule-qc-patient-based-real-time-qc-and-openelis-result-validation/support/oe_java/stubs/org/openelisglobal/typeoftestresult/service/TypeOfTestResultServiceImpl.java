package org.openelisglobal.typeoftestresult.service;
// Stub: the ResultType enum with the upstream DB codes and matches() semantics.
public class TypeOfTestResultServiceImpl {
    public enum ResultType {
        REMARK("R"), DICTIONARY("D"), TITER("T"), NUMERIC("N"), ALPHA("A"), MULTISELECT("M"), CASCADING_MULTISELECT("C");
        final String DBValue;
        ResultType(String v) { DBValue = v; }
        public boolean matches(String type) { return DBValue.equals(type); }
    }
}
