// Bounded probe: where does a JVM report exhaustion of its own configured limits?
// Modes: heap | arraysize | stack | direct
// Each mode catches the VirtualMachineError, prints what was observed, and then
// proves that the program continues by printing "CONTINUED".
import java.nio.ByteBuffer;
import java.util.ArrayList;

public class OomProbe {
    static int depth = 0;

    static void recurse() {
        depth++;
        recurse();
    }

    public static void main(String[] args) throws Exception {
        String mode = args[0];
        long t0 = System.nanoTime();
        switch (mode) {
            case "heap": {
                ArrayList<byte[]> keep = new ArrayList<>();
                try {
                    while (true) {
                        keep.add(new byte[1 << 20]); // 1 MiB each, retained
                    }
                } catch (OutOfMemoryError e) {
                    int n = keep.size();
                    keep = null; // release so the handler can allocate
                    System.out.println("OOME message=\"" + e.getMessage() + "\" retained_MiB=" + n
                        + " maxMemory=" + Runtime.getRuntime().maxMemory());
                }
                break;
            }
            case "arraysize": {
                try {
                    long[] a = new long[Integer.MAX_VALUE];
                    System.out.println("allocated " + a.length);
                } catch (OutOfMemoryError e) {
                    System.out.println("OOME message=\"" + e.getMessage() + "\"");
                }
                break;
            }
            case "stack": {
                try {
                    recurse();
                } catch (StackOverflowError e) {
                    System.out.println("SOE depth=" + depth + " message=" + e.getMessage());
                }
                break;
            }
            case "direct": {
                ArrayList<ByteBuffer> keep = new ArrayList<>();
                try {
                    while (true) {
                        keep.add(ByteBuffer.allocateDirect(1 << 20));
                    }
                } catch (OutOfMemoryError e) {
                    int n = keep.size();
                    keep = null;
                    System.out.println("OOME message=\"" + e.getMessage() + "\" retained_MiB=" + n);
                }
                break;
            }
            default:
                throw new IllegalArgumentException(mode);
        }
        System.out.println("CONTINUED elapsed_ms=" + (System.nanoTime() - t0) / 1_000_000);
    }
}
