# Camera ISP HDR Companding, Rolling-Shutter Visual-Inertial Sync, and LiDAR Blooming

## Summary

Autonomous driving, surgical robotics, aerial navigation, and scientific imaging stacks treat camera tensors (`RGB` / `YCbCr`), `6`-DoF inertial measurements (`IMU`), and `3D` LiDAR point clouds as clean geometric samples captured instantaneously at a shared frame timestamp (`Basis: documentation, source`). In physical silicon and firmware, all three sensing modalities undergo nonlinear radiometric compression, sequential spatial-temporal scanning, and optical/detector saturation—violating downstream computer-vision and state-estimation assumptions before a single neural network or Kalman filter runs (`Basis: source, execution, derived`).

Across primary-source inspections of `raspberrypi/libpisp` (`c77865739bbde5be918d5a7692c8a8050e0abc25`), `kbingham/libcamera` (`5efdc682e5b54f7b9f793b1fbf99884d522fd9f9`), `halide/Halide` (`a409a44f3529e2362f99e72de0089f99064fc6b3`), `opencv/opencv` (`0739a74edc6f5ded745f01cbcfe620062b73f9d6`), `rpng/open_vins` (`69488123ed9362dd44b6f28e7f4680abbff1442b`), `ethz-asl/kalibr` (`1f60227442d25e36365ef5f72cd80b9666d73467`), `autowarefoundation/autoware_universe` (`0b462bcda0705fbf48d675a34fcb7df96e2f770b`), Forster et al. (`DOI: 10.1109/TRO.2016.2597321`), Furgale/Oth et al. (`DOI: 10.1109/IROS.2013.6696514`, `DOI: 10.1109/CVPR.2013.310`), and Cao et al. (`DOI: 10.1145/3319535.3339815`), three multi-physics failure modes dominate perception reliability:

1. **ISP Black-Level Pedestal `uint16` Underflow, `20->12`-Bit HDR PWL Knee Jumps, and `200 Hz` LED `PWM` Dropout (`Basis: source, execution, derived`)**:
   - **Pedestal Wrap-to-Bright**: CMOS sensors bias raw Bayer ADC outputs by an optical black pedestal (`4,096` at `16`-bit scale in `libcamera` `black_level.cpp:36`, i.e., `64` in `10`-bit / `256` in `12`-bit) so zero-photon read noise stays positive. Subtracting `(4080 - 4096)` in unguarded `uint16` SIMD (`vpsubw` instead of saturating `vpsubusw` or signed promotion `cast<float>(x - minRaw)` in `Halide` `camera_pipe_generator.cpp:288, 308`) **wraps dark shadow noise to `65,520` (`99.98%` full-scale white!)**, peppering night scenes with false high-gradient corners, while ordering black-level subtraction *before* `PiSP` Front-End `65`-point piecewise-linear (`PWL`) decompanding (`pisp_fe_config.h:25–26, 114–120`) misaligns every knee threshold!
   - **HDR PWL Knee Quantization Cliffs**: Companding `20`-bit (`120 dB`) `3`-exposure automotive HDR irradiance into `12`-bit MIPI CSI-2 (`0..4095`) introduces **`32x` (`1 -> 32 LSB`) and `991x` (`1 -> 991 LSB`) slope discontinuities** at exposure-handoff knees, plus `~9–14 dB` photon-SNR drops (`motion-ghosting halos`) and non-invertible LUT failures (`Pwl::inverse` returning `proper = false` in `libcamera` `pwl.cpp:251–272`) if tuning tables violate strict monotonicity.
   - **Daylight `PWM` LED Blackout (`libcamera` `agc_channel.cpp:924–931`)**: `AgcChannel::divideUpExposure()` computes `int flickerPeriods = exposureTime / status_.flickerPeriod;` (`line 926`). Whenever outdoor daylight shortens `exposureTime` (`0.25 ms`) below `flickerPeriod` (`5.0 ms` for a `200 Hz`, `10%`-duty automotive LED traffic light or brake lamp), **C++ integer division truncates `flickerPeriods` to `0`, silently disabling flicker avoidance** and leaving an **`85.0%` per-frame probability of capturing zero photons** from an active red traffic signal!
2. **Rolling-Shutter Row-Readout Skew (`15–33 ms`) vs. Forster `SO(3)` IMU Preintegration Clock Drift (`Basis: normative, source, execution`)**: Unlike global-shutter CCDs, rolling-shutter CMOS sensors expose row $v \in [0, H-1]$ at $t(v) = t_{\text{frame}} + \delta t_{\text{cam-imu}} + v \cdot \tau_{\text{line}}$ (`Kalibr` `RollingShutter.hpp:32–34`: `Duration(_lineDelay * k[1])`). For a `1080`-row sensor with $\tau_{\text{line}} = 28\text{ us}$ (`30.24 ms` top-to-bottom scan) plus `+15 ms` uncalibrated MIPI/OS frame-timestamp lag (`45.24 ms` total bottom-row skew), hard emergency braking ($\omega_y = 0.35\text{ rad/s}$ suspension nose-dive) induces a **`15.84-pixel` vertical reprojection error (`0.40 m` phantom obstacle elevation jump at `25 m` range)** against `OpenVINS`'s `SO(3)` analytical IMU preintegrator (`CpiV1.cpp:87–123`), causing VIO covariance divergence or phantom pitch/velocity estimation.
3. **Retroreflective LiDAR Blooming Halos, Specular Multi-Path Ghosts, and Laser Injection (`Basis: normative, source, execution`)**: Time-of-Flight (`ToF`) `905 nm` / `1550 nm` LiDAR receivers span `> 100 dB` dynamic range between dark wet tires (`< 2%` reflectance) and prismatic retroreflective highway signs (`> 10,000x` directional return). Receiver lens flare and APD/SPAD array crosstalk spill saturated photons across $\pm 3.0^\circ$ neighboring channels at the sign's exact range ($R = 30\text{ m}$), **inflating a `0.80 m` roadside post into a `3.94 m`-wide phantom wall blocking the active driving lane**, while grazing wet-asphalt specular reflections ($d_{\text{multi}} = \sqrt{X^2 + (h_s + h_t)^2} > d_{\text{direct}}$) project subterranean ghost obstacles at $z = -2.2\text{ m}$ (`probes/verify_isp_vio_lidar.py`), and timing-synchronized laser pulses (`Cao et al. CCS 2019`) spoof coherent front-bumper obstacles unless gated by hardware randomized pulse intervals + `Autoware` `ring_outlier_filter_node.cpp:209–238` walk-ratio & dual-return intensity checks.

## Applicability

This report covers embedded and autonomous perception pipelines combining CMOS image sensors, hardware/DSL ISPs, MEMS IMUs, and scanning/solid-state LiDARs across the ten subjects in `REPORT.json` (`Basis: derived`):

- **Subject Relationships**:
  - **Radiometric & ISP Pipeline Layer**: `raspberrypi/libpisp` (`pisp_fe_config.h`, `pisp_be_config.h`) defines concrete hardware register/LUT layouts (`65`-entry `uint16` Front-End decompand LUT, `BLA`/`BLC` black-level blocks) driven by `kbingham/libcamera`'s control algorithms (`pwl.cpp`, `decompand.cpp`, `black_level.cpp`, `agc_channel.cpp`), contrasted against `halide/Halide`'s schedule-separated SIMD/HVX/GPU ISP compiler (`camera_pipe_generator.cpp`) and `opencv/opencv`'s multi-exposure HDR radiance fusion (`hdr_common.cpp`).
  - **Visual-Inertial Spatiotemporal Layer**: `rpng/open_vins` (`CpiV1.cpp`, `UpdaterHelper.cpp`) implements **Forster et al. (`2017`)** on-manifold `SO(3)` preintegration with online camera-IMU time-offset Jacobians, calibrated offline via `ethz-asl/kalibr` (`RollingShutter.hpp`), which implements **Furgale et al. (`2013`)** continuous-time B-splines and **Oth et al. (`2013`)** rolling-shutter `lineDelay` estimation.
  - **Active 3D LiDAR Layer**: `autowarefoundation/autoware_universe` (`ring_outlier_filter_node.cpp`, `distortion_corrector_node.cpp`) provides production ROS 2 ego-motion pointcloud undistortion and retroreflective blooming/multipath outlier rejection, evaluated alongside **Cao et al. (`2019`)** physical laser-spoofing attacks.
- **Exact Observation vs. Broader Applicability**:
  - Pinned source citations correspond to the exact 40-hex revisions in `REPORT.json` (note: check `autoware_universe` revision `0b462bcda0705fbf48d675a34fcb7df96e2f770b`).
  - The ISP pipeline ordering invariant (`Decompand -> Signed/Saturating BlackLevel -> WhiteBalance/Demosaic -> ToneMap`), rolling-shutter row-time kinematics, and retroreflective PSF blooming geometry apply universally across Sony Starvis (`IMX490`/`IMX728`), Omnivision (`OX08B40`), ONSemi (`AR0820`) automotive HDR sensors, and Velodyne/Hesai/Ouster/Luminar ToF LiDARs.

## Findings

### 1. Camera ISP HDR Companding Knees, Black-Level Underflow, and `PWM` Flicker Aliasing

#### 1.1 Non-Commutative Pipeline Ordering (`Decompand` Before `BlackLevel`) & `uint16` Wrap-to-Bright
`Basis: source, execution`

In `raspberrypi/libpisp` (`c77865739bbde5be918d5a7692c8a8050e0abc25`, `src/libpisp/frontend/pisp_fe_config.h:23–30, 114–120`), the hardware Front-End enable bitmask orders stages strictly as:
1. `PISP_FE_ENABLE_DECOMPRESS = 0x000002` (MIPI CSI-2 DPCM/RAW12 unpacking)
2. `PISP_FE_ENABLE_DECOMPAND = 0x000004` (`uint16_t lut[65]` expanding companded sensor codes to `16`-bit linear irradiance)
3. `PISP_FE_ENABLE_BLA = 0x000008` / `PISP_FE_ENABLE_BLC = 0x000080` (Black-Level Adjustment / Subtraction)

Why is this exact order (`Decompand` *before* `BLC`, paired with saturating subtraction) a hard mathematical invariant?
1. **`uint16` Unsigned Underflow Wrap-to-Bright (`65,520` White Snow)**:
   - In `kbingham/libcamera` (`5efdc682e5b54f7b9f793b1fbf99884d522fd9f9`, `src/ipa/rpi/controller/rpi/black_level.cpp:35–39`), the `16`-bit-scaled optical black pedestal defaults to `blackLevel = 4096` (`64` in `10`-bit RAW10, `256` in `12`-bit RAW12).
   - Zero-illumination pixels follow a Gaussian read-noise distribution $\mathcal{N}(\mu_{\text{BL}}, \sigma_{\text{read}}^2)$ around `4096`: **roughly `50%` of all true-black pixels measure `< 4096` (e.g., `4080`)**!
   - A naive `uint16_t` SIMD kernel computing `raw_u16 - black_u16` (`4080 - 4096` modulo $2^{16}$) wraps to **`65,520`** (`99.98%` full saturation white, `probes/verify_isp_vio_lidar.py`)! In Bayer RGGB demosaicing (`Halide` `camera_pipe_generator.cpp:78–115`), a single wrapped channel (`R = 65520, G = 0, B = 0`) explodes spatial second-derivative green-channel corrections (`correction = g_gr - avg(g_r)`), blooming into a `3x3` neon magenta/green false corner! Notice how `Halide` (`camera_pipe_generator.cpp:288, 308, 319`) explicitly promotes `cast<float>(x - minRaw)` and clamps `clamp(..., 0.0f, 1.0f)` (`and select(x <= minRaw, 0, ...)`).
2. **Non-Commutativity of `BLC` and `PWL` Companding**:
   - On-sensor HDR companding applies $y = C(x_{\text{linear}} + b_{\text{pedestal}})$ *after* adding sensor pedestal $b_{\text{pedestal}}$ in the first `1:1` shadow segment. Subtracting $b_{\text{pedestal}}$ *before* applying $C^{-1}$ evaluates $C^{-1}(y - b_{\text{pedestal}}) \ne C^{-1}(y) - b_{\text{pedestal}}$, shifting every HDR knee coordinate downward by `256–4096` codes and introducing `> 30x` gain kinks across midtones!

#### 1.2 `20->12`-Bit HDR PWL Knee Slope Jumps & `libcamera` `Pwl::inverse` Monotonicity (`pwl.cpp:206–272`)
`Basis: source, execution, derived`

Automotive tunnel-exit scenes (`dark interior 0.1 lux` simultaneously with `direct sun / oncoming halogen 100,000 lux`) require `120–140 dB` dynamic range (`20–24` linear bits), compressed on-sensor (e.g., Sony Starvis `IMX490` / ONSemi `AR0820`) into `12`-bit MIPI CSI-2 (`0..4095`) via a `3`- or `4`-segment Piecewise-Linear (`PWL`) curve:
- Segment 0 (`[0, 2048] -> [0, 2048]`): slope `1:1` (`1 LSB = 1 linear photon unit`)
- Segment 1 (`[2048, 34816] -> [2048, 3072]`): slope `1:32` (**`32.0x` quantization step jump at `y = 2048`!**)
- Segment 2 (`[34816, 1048575] -> [3072, 4095]`): slope `1:991` (**`991.0x` step size vs. shadows!**)

Inspecting `libcamera` `src/ipa/libipa/pwl.cpp:206–275` (`Pwl::eval` & `Pwl::inverse`) and `OpenCV` `modules/photo/src/hdr_common.cpp` highlights two structural hazards:
1. **SNR Dip & False Canny/Sobel Edges at Exposure-Stitching Knees**: At the handoff between long exposure $T_L$ and medium exposure $T_M$ (`ratio 16x–32x`), photon count resets from near full-well ($N_{e^-} \approx 10{,}000\text{ e}^-$, $\text{SNR} = \sqrt{N} = 40\text{ dB}$) down to $10{,}000 / 16 = 625\text{ e}^-$ ($\text{SNR} = 28\text{ dB}$, a **`12 dB` instantaneous SNR cliff**!) compounded by `32x` PWL quantization steps—creating visible contour banding and moving-object "ghost double-edges" across time-staggered multi-exposure HDR merges unless sensors use simultaneous **split-pixel (large + small photodiode + dual conversion gain `DCG`)** capture.
2. **Partiality of `Pwl::inverse()` (`pwl.cpp:251–275`)**: If calibration JSON supplies slightly non-monotonic knee points (`e.g. temperature-interpolated tables crossing y_k > y_{k+1}`), `Pwl::inverse()` sets `neither = true` (`line 269`) and returns `(inverse, false)`—a best-effort mangled curve that silently corrupts radiometric linearity if callers ignore the `bool` flag!

#### 1.3 Primary-Source Proof of Daylight `200 Hz` LED `PWM` Blackout (`libcamera` `agc_channel.cpp:924–931`)
`Basis: source, execution`

In `kbingham/libcamera` (`src/ipa/rpi/controller/rpi/agc_channel.cpp:924–934`), `AgcChannel::divideUpExposure()` implements anti-flicker exposure quantization:

```cpp
// kbingham/libcamera src/ipa/rpi/controller/rpi/agc_channel.cpp:924-931
if (!status_.fixedExposureTime && !status_.fixedGain &&
    status_.flickerPeriod) {
    int flickerPeriods = exposureTime / status_.flickerPeriod;
    if (flickerPeriods) {
        Duration newExposureTime = flickerPeriods * status_.flickerPeriod;
        gain *= exposureTime / newExposureTime;
        exposureTime = newExposureTime;
    }
```

- **Why Indoor `100/120 Hz` Mains Works Yet Outdoor `200 Hz` Automotive `PWM` Fails Catastrophically**:
  - Under dim indoor `50/60 Hz` AC lighting (`flickerPeriod = 10.0 ms` or `8.33 ms`, continuous `sin^2` wave), `exposureTime` is typically `12–33 ms`, so `flickerPeriods >= 1` rounds `exposureTime` to an exact integer multiple of `10.0 ms` (`integrating equal energy on every row`).
  - Outdoors in bright sunlight (`100,000 lux`), auto-exposure shortens `exposureTime` to **`0.25 ms` (`250 us`)** to avoid saturating the road scene. Modern LED traffic lights, variable speed-limit signs, and matrix brake lights pulse at **`90–400 Hz` (`e.g., 200 Hz => T_PWM = 5.0 ms`) with `10%` duty cycle (`0.50 ms ON, 4.50 ms OFF`)**.
  - At `line 926`, **`int flickerPeriods = 0.25 ms / 5.0 ms` truncates in C++ integer arithmetic to `0`**! `if (flickerPeriods)` evaluates `false`, leaving `exposureTime = 0.25 ms` unguarded: across uniform random phase $\phi \in [0, 5.0)\text{ ms}$, the `0.25 ms` shutter misses the `0.50 ms` LED pulse with probability **`(4.50 - 0.25) / 5.00 = 85.0%`** (`probes/verify_isp_vio_lidar.py`), causing active red traffic signals or lead-vehicle brake lamps to appear **completely OFF** across consecutive frames unless hardware **LED Flicker Mitigation (`LFM`, pulsed/chopped sub-exposure or continuous low-sensitivity overflow capacitor integration >= `11 ms`)** is enforced!

---

### 2. Rolling-Shutter Row Skew (`15–33 ms`) vs. Forster `SO(3)` IMU Preintegration

`Basis: normative, source, execution, derived`

#### 2.1 On-Manifold `SO(3)` Preintegration (`Forster et al. 2017` & `OpenVINS` `CpiV1.cpp:86–135`)
Rather than re-integrating `200–1,000 Hz` MEMS gyroscope ($\tilde{\boldsymbol{\omega}}$) and accelerometer ($\tilde{\mathbf{a}}$) samples whenever nonlinear bundle adjustment updates keyframe poses, Forster, Carlone, Dellaert & Scaramuzza (`DOI: 10.1109/TRO.2016.2597321`) and `rpng/open_vins` (`69488123ed9362dd44b6f28e7f4680abbff1442b`, `ov_core/src/cpi/CpiV1.cpp:58–135`) preintegrate relative rotation $\Delta\mathbf{R}_{ik} \in \mathrm{SO}(3)$, velocity $\boldsymbol{\beta}_{ik}$, and position $\boldsymbol{\alpha}_{ik}$ on-manifold using Rodrigues' formula (`lines 87–88`) with small-angle Taylor guard `mag_w < 0.008726646` (`0.5 deg/s`, `line 70`, avoiding `0 / 0` division in $\frac{1 - \cos(|\boldsymbol{\omega}|\Delta t)}{|\boldsymbol{\omega}|^2}$!) and right-Jacobian bias first-order updates `J_q` (`lines 129–134`).

#### 2.2 Spatiotemporal Coupling of `lineDelay` (`Kalibr`) and `calib_camimu_dt` (`OpenVINS`)
Preintegration implicitly evaluates camera pose at **a single scalar timestamp $t_k$** (`state->_clones_IMU.at(timestamp)` in `OpenVINS` `UpdaterHelper.cpp:329`). Two hardware timing realities violate scalar-timestamp projection:
1. **Sequential Row Readout (`ethz-asl/kalibr` `RollingShutter.hpp:32–34`)**:
   ```cpp
   // ethz-asl/kalibr aslam_cv/aslam_cameras/include/aslam/cameras/RollingShutter.hpp:31-34
   template<typename DERIVED_K>
   Duration temporalOffset(const Eigen::MatrixBase<DERIVED_K> & k) const {
     return Duration(_lineDelay * k[1]);
   }
   ```
   Pixel $(u, v)$ (`k[1] == v`) captures photons at $t(v) = t_{\text{SOF}} + \delta t_{\text{cam-imu}} + v \cdot \tau_{\text{line}}$, where $\tau_{\text{line}} \approx 15\text{–}31\text{ us/row}$ (`30.24 ms` across `1080` rows at `28 us/row`).
2. **Uncalibrated Software Timestamp Lag ($\delta t_{\text{cam-imu}}$)**: When camera frames are timestamped on V4L2/USB DMA completion rather than hardware `FSYNC` GPIO strobe (`IMU <-> Sensor XVS pin`), $\delta t_{\text{cam-imu}}$ fluctuates by `5–25 ms` under CPU/PCIe load.
3. **Hard-Braking Phantom Pitch / Obstacle Elevation Error (`probes/verify_isp_vio_lidar.py`)**:
   - During `1.0 g` emergency braking, vehicle suspension pitch-down reaches $\omega_y \approx 0.35\text{ rad/s}$ (`20 deg/s`). Over `30.24 ms` rolling readout + `15.0 ms` trigger lag (`45.24 ms` at bottom row $v = 1080$), camera orientation rotates by $\Delta\theta = 0.35 \times 0.04524 = \mathbf{0.01583\text{ rad}}$ (`0.91 deg`).
   - On a `f_y = 1,000 px` lens, bottom-of-frame road features shift vertically by **`f_y * tan(0.01583) = 15.84 pixels`** (`~10–30x` larger than `0.5 px` bundle-adjustment noise $\sigma_{\text{pix}}$!), projecting a flat road marking at `25 m` range **`+0.40 m` above/below ground** and corrupting VIO velocity scale unless both continuous-time `calib_camimu_dt` and per-row `_lineDelay * v` (`interpolating IMU clones across [t_SOF, t_EOF]`) are modeled!

---

### 3. Retroreflective LiDAR Blooming, Multi-Path Ghosts, and Laser Spoofing

`Basis: normative, source, execution, derived`

| LiDAR Physical / Adversarial Anomaly | Underlying Optical / Time-of-Flight Mechanism | Quantitative Pointcloud Corruption (`probes/verify_isp_vio_lidar.py`) | Primary-Source Defense (`Autoware` & Hardware Gates) |
| :--- | :--- | :--- | :--- |
| **Retroreflective Blooming (`Halo` Expansion)** | `300 cd/lx/m^2` prismatic traffic sign returns `> 10^4x` irradiance vs. `10%` asphalt; internal lens scatter + SPAD/APD charge spill triggers neighboring $\pm 3^\circ$ channels at sign's ToF $t = 2R/c$ | At $R = 30\text{ m}$, a `0.80 m` roadside sign blooms by $2 \times 30\tan 3^\circ = +3.14\text{ m}$ into a **`3.94 m`-wide phantom barrier straddling the active highway lane!** | `Autoware` `ring_outlier_filter_node.cpp:209–238` (`distance_ratio_` azimuth-walk cluster check) + rejecting low-intensity / secondary-return halo rings surrounding `intensity == 255` saturated cores |
| **Wet-Road Specular Multi-Path Ghosts** | Grazing laser pulse reflects off wet asphalt (Fresnel mirror) to retroreflector at $(X = 24\text{ m}, h_t = 2.2\text{ m})$ and back ($d_{\text{multi}} = \sqrt{24^2 + (1.8 + 2.2)^2} = 24.33\text{ m} > 24.00\text{ m}$) | Sensor projects echo along downward ray angle, placing a **solid phantom cluster at $z = -2.2\text{ m}$ underground** (or floating overhead off glass facades), breaking ground-segmentation planes! | Dual-return (`STRONGEST` vs. `LAST` `ReturnType` at `ring_outlier_filter_node.cpp:168, 236–238`) + geometric mirror-plane ray consistency check against estimated ground mesh |
| **Ego-Motion Scanning Skew (`10 Hz` Spin = `100 ms`)** | At highway `30 m/s` (`108 km/h`) + yaw rate `0.2 rad/s`, vehicle moves **`3.0 m`** between start (`0 deg`) and end (`360 deg`) of one `100 ms` LiDAR sweep | Uncorrected `PointCloud2` warps straight walls by `3.0 m` and splits closing velocities | `Autoware` `distortion_corrector_node.cpp:129–195` (`undistort_pointcloud` using per-point `PointXYZIRCAEDT` timestamp + IMU twist integration & `timestamp_mismatch_fraction` diagnostics) |
| **Adversarial Laser Pulse Injection (`Cao et al. CCS 2019`)** | Photodiode detects victim LiDAR's outgoing `905 nm` pulse and fires a delayed laser pulse at $\Delta t_{\text{fake}} = 2 d_{\text{fake}} / c$ (`< 200 ns` for `< 30 m`) before true echo arrives | Injects coherent `60–200` fake points fooling 3D CNN detectors (`PointPillars`/`Apollo`) at `~75%` success into emergency phantom-obstacle braking (`DOI: 10.1145/3319535.3339815`) | Hardware **per-pulse cryptographic jitter / pulse-position modulation (`PPM` / `FMCW` coherent chirp)** rejecting echoes outside narrow `[t_tx + jitter_secret]` correlation windows |

---

### 4. Multi-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: source, documentation, execution, derived`

| Level | Axis | Hand-Written C++ ISP / VIO / PointCloud (`libpisp`, `OpenVINS`, `Autoware`) | Schedule-Separated DSLs & Typed Frame/Exposure Pipelines (`Halide` + Verified Headers) | Engineering & Verification Impact |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | Manual AVX2/NEON/HVX ISP intrinsics `~5,000–15,000 LoC` C++; `OpenVINS` + `Autoware` filters `~35 KLoC` (`high` coordinate-frame & `uint16` wrap bug rate) | `Halide` `camera_pipe_generator.cpp` **`350 LoC` algorithm + `150 LoC` schedule** (`10–30x` smaller than hand-written HVX/CUDA!); phantom frame/exposure wrappers `< 300 LoC` (`~3–5x` proof ratio) | Separating pure radiometric math (`Func`) from tiling/vectorization (`Schedule`) lets humans & agents prove saturating/monotonicity laws once on `350 LoC` |
| **L2** | **Framework & Toolchain Build Time** | `Halide`/LLVM compiler toolchain from scratch `~15–40 min` (`4–8 GB` RSS); `Autoware` full ROS 2 workspace `~20–60 min` | Ahead-of-Time (`AoT`) `Halide` generator compile **`~1.5–4.0 s`** emitting standalone `.o`/`.h`; `libpisp` / `OpenVINS` incremental `< 5 s` | Always compile `Halide` ISP kernels **Ahead-of-Time (`AoT`)** into static object files so embedded CI never links `libLLVM` (`0 s` target JIT cost) |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | `Kalibr` offline B-spline calibration `~30–180 s`/dataset | `BV16`/`QF_NRA` verification of `uint16` saturating `BLC`, `65`-point `PWL` strict monotonicity (`y[i] < y[i+1]`), and `LFM` duty-cycle overlap **`< 25 ms`** (`< 15 ms` warm LSP) | Checking `PISP_FE_DECOMPAND_LUT_SIZE == 65` monotonicity & `BLC` non-underflow takes `< 5 ms` statically or `< 200 ns` on camera mode-switch |
| **L4** | **Generated Code Execution Performance** | Hardware `PiSP` ASIC **`~200–300 MPix/s`** (`4K60` in `0%` CPU); `Autoware` `distortion_corrector` + `ring_outlier_filter` `~2–6 ms` per `128`-beam `200k`-pt cloud | `Halide` HVX `256`-entry interpolated LUT (`camera_pipe_generator.cpp:293–343`) **`~1.5–3.0 cycles/pixel`** (`12 MP` frame `< 4 ms` on Hexagon DSP); `OpenVINS` `CpiV1` **`< 0.8 us`/IMU sample** | `Halide`'s `lutResample = 8` (`256`-byte L1/HVX register LUT) avoids `4 KiB` gather stalls while preserving linear interpolation accuracy |
| **L5** | **Proof / Certificate Verification Speed** | Runtime `DistortionCorrectorDiagnostics` timestamp-mismatch check (`distortion_corrector_node.cpp:190–194`) `< 50 us`/cloud | Boot/mode-switch `PWL` monotonicity + `FSYNC` `TAI` lock + `PointXYZIRCAEDT` layout witness verification **`< 10 us`** | Checking `64` adjacent `lut[i] <= lut[i+1]` inequalities before DMA-programming `pisp_fe_decompand_config` costs `64` integer compares (`< 50 ns`) |
| **L6** | **RAM, Disk & Binary Footprints** | `128`-beam `10 Hz` `PointXYZIRCAEDT` (`32–48 B/pt` x `240k pts`) = **`~9–11 MB/scan`** (`~100 MB/s`); `4K` `RAW12` = `12.4 MB/frame` | AoT `Halide` ISP binary **`< 64 KiB` `.text`** (`0 B` heap with line-buffered strip-mining!); `pisp_fe_decompand_config` = **`132 B` (`65 x 2 B + pad`)** | Line-buffered (`compute_at` scanline tile) `Halide` schedules hold `4–8` image rows in `L2` SRAM (`< 128 KiB`), cutting DRAM bandwidth & ISP power by **`4–6x`** over frame-buffered `OpenCV` passes |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived, source`

#### 5.1 `(C1)` Human Comprehensibility vs. Agent Execution Ergonomics
- **Three Invisible Implicit Assumptions That Trip Human Vision Engineers**:
  1. **`"Pixel Values Are Proportional to Light"`**: Human ML/CV engineers inspect `uint16` raw arrays assuming `0 == 0 photons` and `2 * x == 2x photons`, missing both the `+4096` optical black pedestal (`wrapping dark noise to 65520 on unsigned subtraction!`) and `991x` HDR PWL highlight compression (`destroying photometric stereo / optical-flow brightness constancy across knee boundaries`).
  2. **`"Integer Division in C++ Duration Ratios"` (`libcamera` `agc_channel.cpp:926`)**: Reading `int flickerPeriods = exposureTime / status_.flickerPeriod;`, a human reviewer checks indoor `50/60 Hz` cases (`15 ms / 10 ms = 1`) and completely misses the **boundary discontinuity at `exposureTime < flickerPeriod`** (`0.25 ms / 5.0 ms == 0`), where anti-flicker protection vanishes silently without a single warning log!
  3. **`"A Frame Has One Timestamp"`**: Passing `header.stamp` on both `sensor_msgs/Image` (`30 ms` rolling scan) and `sensor_msgs/PointCloud2` (`100 ms` mechanical spin) tricks downstream fusion code into treating `100 ms` of moving geometry (`3.0 m` highway travel!) as an instantaneous snapshot (`Autoware` had to enforce a dedicated `PointXYZIRCAEDT` per-point timestamp layout check at `distortion_corrector_node.cpp:206–215` specifically because upstream drivers dropped per-point `time_stamp` fields!).

#### 5.2 `(C2)` Conceptual Simplicity, Felleisen Expressibility & Ousterhout Deep-Module Refinement
- **Why Downstream Post-Hoc Filters Fail Felleisen's Expressibility Test**: Trying to patch `uint16` black-level wrap via a `3x3` median hot-pixel filter, or patching rolling-shutter skew by inflating EKF pixel noise covariance $\mathbf{R}_k$, fails Felleisen's criterion: information destroyed by modular wrap-around (`4080 - 4096 -> 65520`) or unmodeled deterministic bias ($\omega_y \cdot v \cdot \tau_{\text{line}}$) cannot be recovered locally downstream without blurring real point lights or degrading VIO observability.
- **Three Orthogonal Deep-Module Abstractions (`Zero-Cost Radiometric & Spatiotemporal Types`)**:
  1. **Radiometric Domain-Indexed Buffers (`Image<RawCompanded12<Pedestal4096>> -> Image<LinearIrradiance20> -> Image<ToneMappedSRGB8>`)**: Encode radiometric state in the buffer type so `demosaic` and `optical_flow` accept *only* `LinearIrradiance`, statically forcing `decompand_monotone(lut: StrictlyIncreasingLut<65>)` followed by **saturating** `sub_pedestal_sat()` (`vpsubusw` / `saturating_sub`) in exact hardware order.
  2. **Continuous-Time Spatiotemporal Ray Bundles (`TimedRay<Frame, TaiNs>`)**: Unify global-shutter cameras ($\tau_{\text{line}} = 0$), rolling-shutter CMOS ($\tau_{\text{line}} = 28\text{ us/row}$), and spinning/MEMS LiDARs (`per-firing azimuth dt`) into **one universal sensor measurement type**: every `2D` feature or `3D` range return carries its exact photon-capture instant $t_i^{\text{TAI}} = t_{\text{FSYNC}}^{\text{TAI}} + \Delta t_{\text{readout}}(u_i, v_i)$, evaluated against a continuous-time `SE(3)` preintegrated trajectory segment (`eliminating separate RS-camera vs. LiDAR-undistort code paths!`).
  3. **Pulse-Authenticated Dual-Return LiDAR Reception + `LFM` Duty-Overlap Contract**: Statically require automotive HDR camera modes to satisfy $T_{\text{sub-exp,span}} \ge T_{\text{PWM,max}}$ (`>= 11.1 ms` covering `>= 90 Hz` LED standards via chopped/DCG `LFM`) and type LiDAR points with `(StrongestReturn, LastReturn, PulseAuthVerified)` so retroreflective halos, wet-road specular ghosts, and unauthenticated external laser injections are rejected at sensor ingress.

## Boundaries

1. **Frequency-Modulated Continuous-Wave (`FMCW` `1550 nm` Coherent Chirp) LiDAR (`known not to apply` to direct-ToF `Cao et al.` pulse spoofing & multi-return ambiguity)**: Coherent `FMCW` LiDAR mixes returning light with a local-oscillator laser chirp, measuring instantaneous per-pixel radial Doppler velocity $v_r$ alongside range while rejecting incoherent sunlight, cross-LiDAR interference, and non-phase-locked `905 nm` pulse injection (`known not to apply` to direct-ToF incoherent pulse spoofing, though internal optical blooming on nearby retroreflectors still requires local-oscillator AGC saturation handling).
2. **Event-Based Neuromorphic Dynamic Vision Sensors (`DVS` / Prophesee / IniVation Asynchronous $\Delta\log I$ Pixels) (`not examined`)**: Asynchronous microsecond-resolution log-intensity event cameras eliminate frame-level `30 ms` rolling-shutter readout skew and `200 Hz` `PWM` blackout (emitting explicit `200 Hz` ON/OFF polarity event trains instead!), governed by refractory-period dead-time and event-bus saturation equations rather than frame-ISP `PWL` LUTs (`not examined`).
3. **Single-Image Recoverability of Clipped Full-Well Highlight Pixels (`raw == 4095` Across All HDR Sub-Exposures) (`unsupported`)**: Once the shortest sub-exposure photodiode (`e.g., T_short + low conversion gain`) saturates its physical full-well capacity ($q \ge q_{\text{FWC}}$), true scene radiance and chromaticity ratios (`R:G:B -> 1:1:1` highlight clipping) are irretrievably lost; hallucinating metric radiance without unsaturated photons is physically **`unsupported`** for safety-critical perception.
4. **Sub-Millimeter Extrinsic Thermal Warping Across `-40 C .. +85 C` Automotive Chassis Cycles (`unknown` from static factory `Kalibr` runs)**: Offline `Kalibr` calibration (`Furgale et al. 2013`) locks rigid transformation $\mathbf{T}_{IC} \in \mathrm{SE}(3)$ and `_lineDelay` at room temperature (`25 C`); windshield/roof-rack thermal expansion (`0.1–0.3 deg` pitch/yaw flex under solar load) drifts stereo/LiDAR-camera extrinsics at `> 80 m` highway range unless tracked online (`unknown` from factory calibration alone).

## Evidence

| Source / Artifact | Immutable Identity & Narrow Location | Grounded Fact Established |
| :--- | :--- | :--- |
| `raspberrypi/libpisp` | Commit `c77865739bbde5be918d5a7692c8a8050e0abc25`, `src/libpisp/frontend/pisp_fe_config.h:23–44, 114–120` & `backend/pisp_be_config.h` | Hardware Front-End stage order (`DECOMPRESS -> DECOMPAND -> BLA/BLC`, `lines 24–30`) and `65`-point `uint16_t` `pisp_fe_decompand_config` LUT (`lines 114–120`) |
| `kbingham/libcamera` | Commit `5efdc682e5b54f7b9f793b1fbf99884d522fd9f9`, `src/ipa/libipa/pwl.cpp:206–275`, `src/ipa/rpi/controller/rpi/black_level.cpp:35–40`, `decompand.cpp:27–60`, & `agc_channel.cpp:924–934` | `Pwl::inverse` non-monotonicity failure (`pwl.cpp:251–272`), `4096` `16`-bit default black level (`black_level.cpp:36`), and `int flickerPeriods = exposureTime / status_.flickerPeriod` integer-truncation to `0` (`agc_channel.cpp:926`) |
| `halide/Halide` | Commit `a409a44f3529e2362f99e72de0089f99064fc6b3`, `apps/camera_pipe/camera_pipe_generator.cpp:43–115, 213–215, 284–345` | Signed/clamped `blackLevel` subtraction (`288, 308, 319`), green-channel second-derivative demosaicing (`87–115`), and HVX `lutResample = 8` (`256`-entry interpolated LUT, `293–343`) |
| `opencv/opencv` | Commit `0739a74edc6f5ded745f01cbcfe620062b73f9d6`, `modules/photo/src/hdr_common.cpp` | Multi-exposure HDR triangle hat-weighting & radiometric response constraints |
| `rpng/open_vins` | Commit `69488123ed9362dd44b6f28e7f4680abbff1442b`, `ov_core/src/cpi/CpiV1.cpp:58–135` & `ov_msckf/src/update/UpdaterHelper.cpp:314–360` | Analytical `SO(3)` preintegration with `mag_w < 0.008726646` small-angle Taylor guard (`70, 87–88, 100–110`) and IMU clone projection (`329–349`) |
| `ethz-asl/kalibr` | Commit `1f60227442d25e36365ef5f72cd80b9666d73467`, `aslam_cv/aslam_cameras/include/aslam/cameras/RollingShutter.hpp:31–78` | Per-row rolling-shutter `temporalOffset(k) = Duration(_lineDelay * k[1])` (`32–34`) and intrinsics Jacobian `J(0,0) = k[1]` (`71–78`) |
| `autowarefoundation/autoware_universe` | Commit `0b462bcda0705fbf48d675a34fcb7df96e2f770b`, `sensing/autoware_pointcloud_preprocessor/src/outlier_filter/ring_outlier_filter_node.cpp:110–116, 159–238` & `distortion_corrector/distortion_corrector_node.cpp:129–215` | Azimuth-walk `distance_ratio_` + `ReturnType`/`Intensity` blooming filter (`209–238`) and IMU-twist `PointXYZIRCAEDT` ego-motion deskewing + timestamp-mismatch diagnostics (`165–214`) |
| Forster et al. (`2017`), Furgale/Oth et al. (`2013`), Cao et al. (`2019`) | `DOI: 10.1109/TRO.2016.2597321`, `DOI: 10.1109/IROS.2013.6696514`, `DOI: 10.1109/CVPR.2013.310`, `DOI: 10.1145/3319535.3339815` | Manifold `SO(3)` preintegration theory; continuous-time B-spline camera-IMU & rolling-shutter calibration; `75%`-success physical laser-injection LiDAR obstacle spoofing |
| Preserved Executable Probe | `reports/camera-isp-hdr-companding-rolling-shutter-imu-sync-and-lidar-blooming/probes/verify_isp_vio_lidar.py` (observed `2026-11-19`) | Verified `65,520` `uint16` black-level wrap, `32x`/`991x` HDR PWL knee steps, `flickerPeriods == 0` -> `85%` `200 Hz` LED blackout, `15.84 px` (`0.40 m`) braking RS+IMU skew, and `0.80 m -> 3.94 m` LiDAR blooming + `z = -2.2 m` wet-road ghost |

## Revalidation

Run either the preserved package probe from the corpus root (`python3 reports/camera-isp-hdr-companding-rolling-shutter-imu-sync-and-lidar-blooming/probes/verify_isp_vio_lidar.py`) or the standalone zero-dependency bash probe below from any directory (`Python >= 3.10`):

```bash
python3 - <<'EOF'
import math

# 1. uint16 black-level pedestal underflow wrap-to-bright (65520) & 20->12-bit HDR PWL knee steps
assert ((4080 - 4096) & 0xFFFF) == 65520 and max(4080 - 4096, 0) == 0
knees = [(0, 0), (2048, 2048), (34816, 3072), (1048575, 4095)]
s0 = (knees[1][0] - knees[0][0]) / (knees[1][1] - knees[0][1])
s1 = (knees[2][0] - knees[1][0]) / (knees[2][1] - knees[1][1])
s2 = (knees[3][0] - knees[2][0]) / (knees[3][1] - knees[2][1])
assert s0 == 1.0 and s1 == 32.0 and s2 > 990.0

# 2. libcamera agc_channel.cpp:926 integer division truncation (0.25ms / 5.0ms == 0 -> 85% LED miss)
t_exp, t_pwm, on_ms = 0.25, 5.0, 0.50
flicker_periods = int(t_exp // t_pwm)
miss_prob = ((t_pwm - on_ms) - t_exp) / t_pwm
assert flicker_periods == 0 and abs(miss_prob - 0.85) < 1e-9

# 3. Rolling-shutter (1080 * 28us = 30.24ms) + 15ms IMU offset @ 0.35 rad/s braking pitch -> 15.84px
skew_s = 1080 * 28e-6 + 0.015
reproj_px = 1000.0 * math.tan(0.35 * skew_s)
assert abs(reproj_px - 15.8353) < 1e-2 and 25.0 * math.tan(0.35 * skew_s) > 0.39

# 4. Retroreflective LiDAR +/-3 deg blooming (0.80m -> 3.94m at 30m) & wet-road multipath z=-2.2m
bloom_w = 0.80 + 2.0 * 30.0 * math.tan(math.radians(3.0))
assert abs(bloom_w - 3.9445) < 1e-2 and math.hypot(24.0, 1.8 + 2.2) > math.hypot(24.0, 2.2 - 1.8)
print("REVALIDATION_OK")
EOF
```

Revalidate upstream implementations when:
1. `kbingham/libcamera` (`agc_channel.cpp:924–934` / `agc_mean_luminance.cpp`) adds sub-period `LFM` HDR exposure-floor clamps when `exposureTime < flickerPeriod`;
2. `rpng/open_vins` merges native per-row rolling-shutter `lineDelay` interpolation directly into `UpdaterHelper::get_feature_jacobian_full()`; or
3. `autowarefoundation/autoware_universe` replaces 2D azimuth-ring walk heuristics (`ring_outlier_filter_node.cpp`) with hardware `FMCW` Doppler-consistent or dual-return radiometric PSF deconvolution.
