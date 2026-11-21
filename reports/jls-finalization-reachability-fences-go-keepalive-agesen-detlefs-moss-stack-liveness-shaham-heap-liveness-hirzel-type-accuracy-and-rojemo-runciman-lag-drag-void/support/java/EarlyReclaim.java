// Probe: can a Java object be reclaimed (and its Cleaner action run) while one of
// its own instance methods is still executing, after the method's last use of
// `this`? Compare with Reference.reachabilityFence(this) in a finally block.
//
// Each Resource registers a Cleaner action that marks its slot in `freed`.
// actionNoFence()/actionFence() read this.idx (the last use of `this`), force
// several GC cycles while still inside the method, then report whether the
// cleaning action already ran.
//
// Usage: java EarlyReclaim <nofence|fence> <trials>
import java.lang.ref.Cleaner;
import java.lang.ref.Reference;
import java.util.concurrent.atomic.AtomicIntegerArray;

public class EarlyReclaim {
    static final Cleaner CLEANER = Cleaner.create();
    static final AtomicIntegerArray freed = new AtomicIntegerArray(100000);

    static final class Release implements Runnable {
        private final int idx;
        Release(int idx) { this.idx = idx; }
        public void run() { freed.set(idx, 1); }
    }

    static final class Resource {
        final int idx;
        Resource(int idx) {
            this.idx = idx;
            CLEANER.register(this, new Release(idx));
        }

        int actionNoFence() {
            int i = this.idx;          // last use of `this`
            gcAndWait();
            return freed.get(i);       // 1 => cleaned while still inside a method of this object
        }

        int actionFence() {
            try {
                int i = this.idx;
                gcAndWait();
                return freed.get(i);
            } finally {
                Reference.reachabilityFence(this);
            }
        }
    }

    static void gcAndWait() {
        for (int k = 0; k < 3; k++) {
            System.gc();
            try { Thread.sleep(20); } catch (InterruptedException e) { throw new RuntimeException(e); }
        }
    }

    public static void main(String[] args) {
        boolean fence = args[0].equals("fence");
        int trials = Integer.parseInt(args[1]);
        int early = 0;
        int first = -1;
        for (int t = 0; t < trials; t++) {
            int r = fence ? new Resource(t).actionFence() : new Resource(t).actionNoFence();
            if (r == 1 && first < 0) first = t;
            early += r;
        }
        System.out.println("java=" + Runtime.version() + " mode=" + args[0]
                + " trials=" + trials + " cleaned_while_method_running=" + early
                + " first_early_trial=" + first);
    }
}
