package org.openelisglobal.qc.valueholder;
import java.math.BigDecimal;
// Stub data holder exposing only the getters the evaluators call.
public class QCResult {
    private final String id; private final BigDecimal value; private final BigDecimal z;
    public QCResult(String id, BigDecimal value, BigDecimal z) { this.id = id; this.value = value; this.z = z; }
    public String getId() { return id; }
    public BigDecimal getResultValue() { return value; }
    public BigDecimal getZScore() { return z; }
}
