import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import org.openelisglobal.qc.service.evaluator.*;
import org.openelisglobal.qc.valueholder.*;
import org.openelisglobal.result.valueholder.Result;
import org.openelisglobal.resultlimits.valueholder.ResultLimit;
import org.openelisglobal.resultvalidation.util.ValidationSignals;

/** Conformance probe: feeds edge-case inputs to unmodified OpenELIS evaluator / validation classes. */
public class Probe {
    static BigDecimal d(String s) { return s == null ? null : new BigDecimal(s); }
    static QCResult r(String id, String v, String z) { return new QCResult(id, d(v), d(z)); }
    static String show(RuleEvaluationResult x) {
        return String.format("violated=%s evaluated=%s severity=%s msg=%s", x.isViolated(), x.isEvaluated(), x.getSeverity(), x.getMessage());
    }
    static List<QCResult> hist(int n, String v) { List<QCResult> h = new ArrayList<>(); for (int i = 0; i < n; i++) h.add(r("h" + i, v, null)); return h; }

    public static void main(String[] a) {
        System.out.println("java " + System.getProperty("java.version"));
        Rule1_3sEvaluator r13 = new Rule1_3sEvaluator(); Rule2_2sEvaluator r22 = new Rule2_2sEvaluator();
        RuleR_4sEvaluator rR4 = new RuleR_4sEvaluator(); Rule4_1sEvaluator r41 = new Rule4_1sEvaluator();
        Rule10_xEvaluator r10 = new Rule10_xEvaluator(); Rule1_2sEvaluator r12 = new Rule1_2sEvaluator();
        QCStatistics ok = new QCStatistics(d("100"), d("2"));
        QCStatistics zeroSd = new QCStatistics(d("100"), d("0"));
        QCStatistics nullSd = new QCStatistics(d("100"), null);

        System.out.println("\n## Westgard evaluators (mean 100, SD 2 unless noted; z computed from value when no stored z)");
        System.out.println("W1 1_3s value 106.0 (z=+3.0 exactly)         : " + show(r13.evaluate(r("c", "106.0", null), hist(0, "100"), ok)));
        System.out.println("W2 1_3s value 105.98 (z=+2.99)               : " + show(r13.evaluate(r("c", "105.98", null), hist(0, "100"), ok)));
        System.out.println("W3 1_3s value 200 with SD=0                  : " + show(r13.evaluate(r("c", "200", null), hist(0, "100"), zeroSd)));
        System.out.println("W4 1_3s value 200 with SD=null               : " + show(r13.evaluate(r("c", "200", null), hist(0, "100"), nullSd)));
        System.out.println("W5 10x current 50, 9 history 300, SD=0       : " + show(r10.evaluate(r("c", "50", null), hist(9, "300"), zeroSd)));
        System.out.println("W6 10x current 100 (=mean), 9 history 99     : " + show(r10.evaluate(r("c", "100", null), hist(9, "99"), ok)));
        System.out.println("W7 10x current 100 (=mean), 9 history 101    : " + show(r10.evaluate(r("c", "100", null), hist(9, "101"), ok)));
        List<QCResult> p = new ArrayList<>(); p.add(r("prev", "106", null));
        System.out.println("W8 R4s prev z=+3.0, curr z=-1.0 (range 4.0) : " + show(rR4.evaluate(r("c", "98", null), p, ok)));
        List<QCResult> p2 = new ArrayList<>(); p2.add(r("prev", "104.2", null));
        System.out.println("W9 R4s prev z=+2.1, curr z=-2.1 (range 4.2) : " + show(rR4.evaluate(r("c", "95.8", null), p2, ok)));
        System.out.println("W10 2_2s with empty history                  : " + show(r22.evaluate(r("c", "105", null), hist(0, "100"), ok)));
        System.out.println("W11 2_2s with null statistics                : " + show(r22.evaluate(r("c", "105", null), hist(1, "105"), null)));
        System.out.println("W12 1_3s stored z=0.5 although value 200     : " + show(r13.evaluate(r("c", "200", "0.5"), hist(0, "100"), ok)));
        List<QCResult> h41 = new ArrayList<>(); h41.add(r("a", "102.2", null)); h41.add(r("b", "102.2", null)); h41.add(r("c0", "102.2", null));
        System.out.println("W13 4_1s four at z=+1.1                      : " + show(r41.evaluate(r("c", "102.2", null), h41, ok)));
        System.out.println("W14 1_2s value 104.0 (z=+2.0)                : " + show(r12.evaluate(r("c", "104.0", null), hist(0, "100"), ok)));
        System.out.println("W15 canEvaluate(config code '1-3s')          : " + r13.canEvaluate(new WestgardRuleConfig("1-3s", true)));
        System.out.println("W16 canEvaluate(config code '1\u2083\u209b')            : " + r13.canEvaluate(new WestgardRuleConfig("1\u2083\u209b", true)));

        System.out.println("\n## ValidationSignals.resultFlag / isClearAtEntry (authored limit: valid 0..20, normal 3.5..5.1, critical <2.5 or >6.5)");
        ResultLimit lim = new ResultLimit(); lim.setId("L1"); lim.setLowValid(0); lim.setHighValid(20);
        lim.setLowNormal(3.5); lim.setHighNormal(5.1); lim.setLowCritical(2.5); lim.setHighCritical(6.5);
        String[] vals = {"4.0", "5.5", "7.0", "25", "-1", "<0.5", ">20", "5\u00d710\u2070", "7\u00d710\u2070", "7e0", "NaN", "Infinity", "", "4,0", " 4.0 "};
        for (String v : vals) {
            String flag = ValidationSignals.resultFlag(lim, "N", v);
            boolean clearNoQc = ValidationSignals.isClearAtEntry(lim, "N", v, ValidationSignals.QC_UNKNOWN, false, false, false);
            boolean critR = ValidationSignals.isCritical(lim, new Result("N", v));
            System.out.printf("V value=%-12s flag=%-9s isCritical(Result)=%-5s clearAtEntry(QC UNKNOWN)=%s%n", "'" + v + "'", flag, critR, clearNoQc);
        }
        System.out.println("V in-range 4.0 with QC_FAIL clear?            : " + ValidationSignals.isClearAtEntry(lim, "N", "4.0", ValidationSignals.QC_FAIL, false, false, false));
        System.out.println("V in-range 4.0 with QC_PASS clear?            : " + ValidationSignals.isClearAtEntry(lim, "N", "4.0", ValidationSignals.QC_PASS, false, false, false));
        ResultLimit upperOnly = new ResultLimit(); upperOnly.setId("L2"); upperOnly.setHighNormal(5.1);
        System.out.println("V upper-only limit, value -5 flag/clear       : " + ValidationSignals.resultFlag(upperOnly, "N", "-5") + " / "
                + ValidationSignals.isClearAtEntry(upperOnly, "N", "-5", ValidationSignals.QC_UNKNOWN, false, false, false));
        ResultLimit unauthored = new ResultLimit();
        System.out.println("V synthetic empty limit (id null) flag/clear  : " + ValidationSignals.resultFlag(unauthored, "N", "4.0") + " / "
                + ValidationSignals.isClearAtEntry(unauthored, "N", "4.0", ValidationSignals.QC_UNKNOWN, false, false, false));
        System.out.println("V default ResultLimit lowCritical/highCritical: " + unauthored.getLowCritical() + " / " + unauthored.getHighCritical());
        System.out.println("V isModified('2'), ('x'), (null)              : " + ValidationSignals.isModified("2") + " " + ValidationSignals.isModified("x") + " " + ValidationSignals.isModified(null));
        System.out.println("V isNceOpen(null), ('Closed'), ('closed')     : " + ValidationSignals.isNceOpen(null) + " " + ValidationSignals.isNceOpen("Closed") + " " + ValidationSignals.isNceOpen("closed"));
        java.sql.Timestamp ts = new java.sql.Timestamp(1000L);
        System.out.println("V isStale(null), ('abc'), ('1000')            : " + ValidationSignals.isStale(null, ts) + " " + ValidationSignals.isStale("abc", ts) + " " + ValidationSignals.isStale("1000", ts));
    }
}
