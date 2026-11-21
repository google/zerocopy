import java.io.FileInputStream;
import java.io.IOException;

/** Correlated-branch resource patterns. Methods named *Safe never leak;
 *  methods named *Bug leak on some path. */
public class Corr {

  /** Safe: exactly one of the two correlated branches closes the stream. */
  static void corrCloseSafe(String name, boolean b) throws IOException {
    FileInputStream f = new FileInputStream(name);
    if (b) f.close();
    if (!b) f.close();
  }

  /** Safe: a flag records whether the stream was closed. */
  static void flagCloseSafe(String name, boolean b) throws IOException {
    FileInputStream f = new FileInputStream(name);
    boolean closed = false;
    if (b) { f.close(); closed = true; }
    if (!closed) f.close();
  }

  /** Safe: the stream is only opened when it is later closed. */
  static void corrOpenSafe(String name, boolean b) throws IOException {
    FileInputStream f = null;
    if (b) f = new FileInputStream(name);
    if (b) f.close();
  }

  /** Safe: straight-line open and close (no correlation needed). */
  static void plainSafe(String name) throws IOException {
    FileInputStream f = new FileInputStream(name);
    f.close();
  }

  /** Bug: leaks on the path where b is false. */
  static void leakBug(String name, boolean b) throws IOException {
    FileInputStream f = new FileInputStream(name);
    if (b) f.close();
  }
}
