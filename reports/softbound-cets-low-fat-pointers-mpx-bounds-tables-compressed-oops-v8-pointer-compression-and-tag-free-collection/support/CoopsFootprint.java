// Measures retained heap bytes per object/reference and a pointer-chasing
// traversal time under whatever HotSpot flags the JVM was started with.
// Usage: java CoopsFootprint <nodes>
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;

public final class CoopsFootprint {
    static final class Node {      // one reference field + one int field
        Node next;
        int value;
    }

    static final class Pair {      // two reference fields + one int field
        Pair left, right;
        int value;
    }

    static long usedAfterGc(MemoryMXBean mx) {
        for (int i = 0; i < 4; i++) {
            System.gc();
            try { Thread.sleep(50); } catch (InterruptedException e) { throw new RuntimeException(e); }
        }
        return mx.getHeapMemoryUsage().getUsed();
    }

    public static void main(String[] args) {
        int n = Integer.parseInt(args[0]);
        MemoryMXBean mx = ManagementFactory.getMemoryMXBean();

        long before = usedAfterGc(mx);
        Node head = null;
        for (int i = 0; i < n; i++) { Node x = new Node(); x.value = i; x.next = head; head = x; }
        long afterList = usedAfterGc(mx);

        Pair[] pairs = new Pair[n];
        long afterPairArray = usedAfterGc(mx);
        for (int i = 0; i < n; i++) { Pair p = new Pair(); p.value = i; pairs[i] = p; }
        long afterPairs = usedAfterGc(mx);
        long keep = pairs[n - 1].value + (long) pairs.length;   // keeps the Pair array live across the measurement
        pairs = null;
        long afterPairsFreed = usedAfterGc(mx);

        Object[] refs = new Object[n];          // n reference slots, all null
        long afterArray = usedAfterGc(mx);
        long arrayBase = afterPairsFreed;

        Object[] plain = new Object[n];         // n distinct java.lang.Object instances
        for (int i = 0; i < n; i++) plain[i] = new Object();
        long afterObjects = usedAfterGc(mx);

        // Pointer-chasing traversal; report the best of 7 timed passes after 3 warm-ups.
        long best = Long.MAX_VALUE, sink = 0;
        for (int pass = 0; pass < 10; pass++) {
            long t0 = System.nanoTime();
            long s = 0;
            for (Node x = head; x != null; x = x.next) s += x.value;
            long dt = System.nanoTime() - t0;
            sink += s;
            if (pass >= 3) best = Math.min(best, dt);
        }

        System.out.printf("bytes_per_Node=%.2f%n", (afterList - before) / (double) n);
        System.out.printf("bytes_per_Pair=%.2f%n", (afterPairs - afterPairArray) / (double) n);
        System.out.printf("bytes_per_array_slot=%.2f%n", (afterArray - arrayBase) / (double) n);
        System.out.printf("bytes_per_Object=%.2f%n", (afterObjects - afterArray) / (double) n - (afterArray - arrayBase) / (double) n);
        System.out.printf("traverse_ns_per_node_best=%.3f%n", best / (double) n);
        System.out.println("vm.compressedOopsMode=" + System.getProperty("java.vm.compressedOopsMode"));
        if (sink == 42 && keep == 42 && refs.length == 0 && plain.length == 0) System.out.println("unreachable");
    }
}
