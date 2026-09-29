import time
from pathlib import Path
Path("entered").write_text("1")
while not Path("release").exists(): time.sleep(.01)
