package org.openelisglobal.qc.valueholder;
import java.math.BigDecimal;
// Stub data holder.
public class QCStatistics {
    private final BigDecimal mean, sd;
    public QCStatistics(BigDecimal mean, BigDecimal sd) { this.mean = mean; this.sd = sd; }
    public BigDecimal getMean() { return mean; }
    public BigDecimal getStandardDeviation() { return sd; }
}
