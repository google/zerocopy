import com.google.publicalerts.cap.Alert;
import com.google.publicalerts.cap.CapException;
import com.google.publicalerts.cap.CapXmlParser;
import com.google.publicalerts.cap.Reason;
import com.google.publicalerts.cap.Reasons;
import com.google.publicalerts.cap.profile.CapProfile;
import com.google.publicalerts.cap.profile.GoogleProfile;
import com.google.publicalerts.cap.profile.us.Ipaws1Profile;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Arrays;

/**
 * Runs every *.xml case in a directory through the CAP library parser (which
 * applies the extended XSD and then the library CapValidator), then through
 * the IPAWS v1.0 and Google profiles. Prints one line per case:
 *   case | parse outcome | reason types (level:type) | IPAWS reasons | Google reasons
 * Usage: java -cp <classes>:<jars> CapProbe <dir>
 */
public class CapProbe {
  static String fmt(Reasons rs) {
    StringBuilder sb = new StringBuilder();
    for (Reason r : rs) {
      if (sb.length() > 0) sb.append(' ');
      sb.append(r.getLevel().name().charAt(0)).append(':').append(r.getType());
    }
    return sb.length() == 0 ? "-" : sb.toString();
  }

  public static void main(String[] args) throws Exception {
    File[] files = new File(args[0]).listFiles((d, n) -> n.endsWith(".xml"));
    Arrays.sort(files);
    CapProfile ipaws = new Ipaws1Profile();
    CapProfile google = new GoogleProfile();
    long t0 = System.nanoTime();
    for (File f : files) {
      String xml = new String(Files.readAllBytes(f.toPath()), StandardCharsets.UTF_8);
      String name = f.getName().replace(".xml", "");
      Reasons.Builder rb = Reasons.newBuilder();
      Alert alert = null;
      String outcome;
      try {
        alert = new CapXmlParser(false).parseFrom(xml, rb);
        Reasons rs = rb.build();
        outcome = rs.containsWithLevelOrHigher(Reason.Level.ERROR) ? "ERROR-REASONS" : "ACCEPTED";
      } catch (Throwable t) {
        outcome = "EXCEPTION " + t.getClass().getSimpleName() + ": " + String.valueOf(t.getMessage()).replace('\n', ' ');
      }
      String core = fmt(rb.build());
      String ip = "-", go = "-";
      if (alert != null) {
        try { ip = fmt(ipaws.validate(alert)); } catch (Throwable t) { ip = "EXCEPTION " + t.getClass().getSimpleName(); }
        try { go = fmt(google.validate(alert)); } catch (Throwable t) { go = "EXCEPTION " + t.getClass().getSimpleName(); }
      }
      System.out.println(name + " | " + outcome + " | " + core + " | IPAWS: " + ip + " | GOOGLE: " + go);
    }
    long t1 = System.nanoTime();
    // Throughput: re-parse the baseline case many times (warm JVM).
    String base = new String(Files.readAllBytes(new File(args[0], "c01_valid_baseline.xml").toPath()), StandardCharsets.UTF_8);
    int n = 5000;
    for (int i = 0; i < 1000; i++) new CapXmlParser(true).parseFrom(base);
    long t2 = System.nanoTime();
    for (int i = 0; i < n; i++) new CapXmlParser(true).parseFrom(base);
    long t3 = System.nanoTime();
    System.out.printf("TIMING first pass over %d cases (cold JVM): %.1f ms%n", files.length, (t1 - t0) / 1e6);
    System.out.printf("TIMING warm parse+validate of baseline: n=%d mean=%.1f us/message%n", n, (t3 - t2) / 1e3 / n);
  }
}
