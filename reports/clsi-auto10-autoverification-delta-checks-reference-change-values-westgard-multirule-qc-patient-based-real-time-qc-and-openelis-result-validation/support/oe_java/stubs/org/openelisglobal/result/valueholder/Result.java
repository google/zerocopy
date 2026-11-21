package org.openelisglobal.result.valueholder;
// Stub: a result with a type code and a raw value string.
public class Result {
    private final String type, value;
    public Result(String type, String value) { this.type = type; this.value = value; }
    public String getResultType() { return type; }
    public String getValue() { return value; }
    public String getValue(boolean b) { return value; }
}
