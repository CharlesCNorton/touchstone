# Bugs

Crashes found by `touchstone scan` in third-party code.

## TheAlgorithms/Python

- `maths/modular_division.py` — `greatest_common_divisor(5, 0)` → ZeroDivisionError: integer modulo by zero
- `maths/interquartile_range.py` — `interquartile_range([5])` → IndexError: list index out of range
- `maths/perfect_square.py` — `perfect_square(-5)` → ValueError: math domain error
- `maths/least_common_multiple.py` — `least_common_multiple_slow(0, 5)` → ZeroDivisionError: integer modulo by zero ([#14845](https://github.com/TheAlgorithms/Python/pull/14845))
- `maths/binary_multiplication.py` — `binary_mod_multiply(1, 1, 0)` → ZeroDivisionError: integer modulo by zero
- `maths/modular_exponential.py` — `modular_exponential(2, 3, 0)` → ZeroDivisionError: integer modulo by zero
- `maths/area.py` — `area_triangle_three_sides` near-degenerate float triangle → ValueError: math domain error
- `maths/greatest_common_divisor.py` — module import (line 76 `except IndexError, UnboundLocalError, ValueError:`) → SyntaxError: multiple exception types must be parenthesized

## huggingface/huggingface_hub

- `src/huggingface_hub/utils/_paths.py` — `filter_repo_objects(["a.txt"], allow_patterns=[""])` → IndexError: string index out of range ([#4402](https://github.com/huggingface/huggingface_hub/pull/4402))

## huggingface/transformers

- `src/transformers/integrations/finegrained_fp8.py` — `_cdiv(1, 0)` → ZeroDivisionError: integer division or modulo by zero
- `src/transformers/audio_utils.py` — `window_function(window_length=-1, frame_length=-1)` → ValueError: negative dimensions are not allowed

## huggingface/trl

- `trl/trainer/utils.py` — `compute_mfu(100e9, 1000.0, 0)` → ZeroDivisionError: float division by zero ([#6174](https://github.com/huggingface/trl/pull/6174))

## huggingface/pytorch-image-models

- `timm/utils/metrics.py` — `AverageMeter().update(1.0, n=0)` → ZeroDivisionError: float division by zero ([#2709](https://github.com/huggingface/pytorch-image-models/pull/2709))

## mistralai/mistral-common

- `src/mistral_common/tokens/tokenizers/audio.py` — `AudioConfig(sampling_rate=1, frame_rate=2.0)` padding path (`raw_audio_length_per_tok == 0`) → ZeroDivisionError: integer modulo by zero ([#253](https://github.com/mistralai/mistral-common/pull/253))

## lucidrains/vit-pytorch

- `vit_pytorch/pit.py` — `conv_output_size(224, 16, 0)` → ZeroDivisionError: division by zero ([#367](https://github.com/lucidrains/vit-pytorch/pull/367))
- `vit_pytorch/t2t.py` — `conv_output_size(224, 16, 0, 0)` → ZeroDivisionError: division by zero ([#367](https://github.com/lucidrains/vit-pytorch/pull/367))

## networkx/networkx

- `networkx/readwrite/graph6.py` — `from_graph6_bytes(b"")` → IndexError: list index out of range ([#8723](https://github.com/networkx/networkx/pull/8723))

## benhamner/Metrics

- `Python/ml_metrics/elementwise.py` — `ce([], [])` → ZeroDivisionError: division by zero

## python/cpython

- `Lib/colorsys.py` — `rgb_to_hsv(-1, 0, -2)` → ZeroDivisionError: division by zero
- `Lib/turtle.py` — `TNavigator().degrees(0)` → ZeroDivisionError: division by zero ([#152038](https://github.com/python/cpython/pull/152038))

## ArduPilot/pymavlink

- `tools/magfit_motors.py` — `radius(d=[], offsets=7, motor_ofs=7)` → ValueError: not enough values to unpack (expected 2, got 0)

## RocketPy-Team/RocketPy

- `rocketpy/tools.py` — `bilinear_interpolation(x=0, y=0, x1=0, x2=0, y1=0, y2=0, z11=0, z12=0, z21=0, z22=0)` → ZeroDivisionError
- `rocketpy/tools.py` — `calculate_cubic_hermite_coefficients(x0=0, x1=0, y0=0, yp0=0, y1=0, yp1=0)` → ZeroDivisionError: float division by zero
- `rocketpy/tools.py` — `geopotential_height_to_geometric_height(geopotential_height=0, radius=0)` → ZeroDivisionError
- `rocketpy/utilities.py` — `compute_cd_s_from_drop_test(terminal_velocity=0, rocket_mass=0, air_density=0, g=0)` → ZeroDivisionError: division by zero

## USEPA/WNTR

- `wntr/utils/polynomial_interpolation.py` — `cubic_spline(x1=0, x2=0, f1=0, f2=0, df1=0, df2=0)` → ZeroDivisionError: division by zero

## Unidata/MetPy

- `src/metpy/interpolate/geometry.py` — `circumcenter(pt0=[], pt1=[], pt2=[-2, 8, 2, 1])` → IndexError: list index out of range
- `src/metpy/interpolate/geometry.py` — `triangle_area(pt1=[], pt2=[], pt3=[-2, 8, 2, 1])` → IndexError: list index out of range
- `src/metpy/interpolate/grid.py` — `get_xy_range(bbox={})` → KeyError: 'east'
- `src/metpy/interpolate/tools.py` — `cressman_weights(sq_dist=0, r=0)` → ZeroDivisionError: division by zero

## biopython/biopython

- `Bio/Blast/NCBIXML.py` — `fmt_(value=0, format_spec=0, default_str=0)` → ZeroDivisionError: integer modulo by zero
- `Bio/Data/CodonTable.py` — `make_back_table(table=[-2, 8, 2, 1], default_stop_codon=-1)` → IndexError: list index out of range
- `Bio/PDB/Polypeptide.py` — `index_to_one(index=0)` → KeyError: 0
- `Bio/PDB/Polypeptide.py` — `index_to_three(i=0)` → KeyError: 0
- `Bio/PDB/Polypeptide.py` — `one_to_index(s=0)` → KeyError: 0
- `Bio/PDB/Polypeptide.py` — `three_to_index(s=0)` → KeyError: 0
- `Bio/Pathway.py` — `System().remove_reaction(reaction=0)` → KeyError
- `Bio/Phylo/PhyloXMLIO.py` — `_local(tag=[])` → IndexError: list index out of range
- `Bio/SearchIO/BlatIO.py` — `_calc_score(psl={}, is_protein=7)` → KeyError: 'matches'
- `Bio/SeqIO/SffIO.py` — `_get_read_region(read_name=[])` → IndexError: list index out of range

## commaai/openpilot

- `openpilot/common/transformations/transformations.py` — `quat2rot_single(q=[])` → ValueError: not enough values to unpack (expected 4, got 0)
- `openpilot/selfdrive/locationd/helpers.py` — `parabolic_peak_interp(R=[], max_index=7)` → IndexError: list index out of range ([#38250](https://github.com/commaai/openpilot/pull/38250))
- `openpilot/selfdrive/modeld/compile_modeld.py` — `sample_skip(buf=[-8, -3, 7, -3], frame_skip=0)` → ValueError: slice step cannot be zero
- `openpilot/system/camerad/cameras/nv12_info.py` — `align(val=0, alignment=0)` → ZeroDivisionError: integer division or modulo by zero

## google/deepvariant

- `deepvariant/dv_utils.py` — `int_tensor_to_string(x=[])` → IndexError: list index out of range
- `deepvariant/variant_caller.py` — `_quantize_gq(raw_gq=1, binsize=0)` → ZeroDivisionError: integer division or modulo by zero
- `deepvariant/variant_caller.py` — `_rescale_read_counts_if_necessary(n_ref_reads=0, n_total_reads=0, max_allowed_reads=-1)` → ZeroDivisionError: float division by zero
- `deepvariant/vcf_stats.py` — `_format_histogram_for_vega(counts=[-2, 8, 2, 1], bins=[5, 8])` → IndexError: list index out of range

## nipy/nibabel

- `nibabel/quaternions.py` — `mult(q1=[], q2=[])` → ValueError: not enough values to unpack (expected 4, got 0)

## pysam-developers/pysam

- `pysam/Pileup.py` — `decodeGenotype(code=0)` → KeyError: 0

## tidepool-org/PyLoopKit

- `pyloopkit/carb_math.py` — `carb_glucose_effect(carb_start=-1, carb_value=0, at_date=2, carb_ratio=0, insulin_sensitivity=7, default_absorption_time=62, delay=-56, carb_absorption_time=2)` → ZeroDivisionError: division by zero ([#30](https://github.com/tidepool-org/PyLoopKit/pull/30))
- `pyloopkit/carb_math.py` — `parabolic_absorbed_carbs(total=0, time=0, absorption_time=0)` → ZeroDivisionError: division by zero ([#30](https://github.com/tidepool-org/PyLoopKit/pull/30))
- `pyloopkit/carb_math.py` — `parabolic_percent_absorption_at_time(time=0, absorption_time=0)` → ZeroDivisionError: division by zero ([#30](https://github.com/tidepool-org/PyLoopKit/pull/30))
- `pyloopkit/dose_math.py` — `as_bolus(correction=[], pending_insulin=7, max_bolus=7, volume_rounder=7)` → IndexError: list index out of range
- `pyloopkit/insulin_math.py` — `is_continuous(reservoir_dates=[-3, -3], unit_volumes=[3, -9, 1, 2], start=2, end=7, maximum_duration=1)` → IndexError: list index out of range
- `pyloopkit/pyloop_parser.py` — `get_basal_schedule(data=[])` → IndexError: pop from empty list
- `pyloopkit/pyloop_parser.py` — `get_carb_ratios(data=[])` → IndexError: pop from empty list
- `pyloopkit/pyloop_parser.py` — `get_sensitivities(data=[])` → IndexError: pop from empty list
- `pyloopkit/pyloop_parser.py` — `get_starts_and_ends_from_seconds(seconds_list=[])` → IndexError: pop from empty list
- `pyloopkit/pyloop_parser.py` — `get_target_range_schedule(data=[])` → IndexError: pop from empty list

## e2nIEE/pandapower

- `pandapower/converter/powerfactory/pp_import_functions.py` — `map_sgen_type_var(pf_sgen_type=-1)` → KeyError: -1
- `pandapower/converter/powerfactory/pp_import_functions.py` — `map_type_var(pf_load_type=0)` → KeyError: 0
- `pandapower/diagnostic/diagnostic_helpers.py` — `check_boolean(element=[], element_index=7, column=7)` → IndexError: list index out of range
- `pandapower/diagnostic/diagnostic_helpers.py` — `check_switch_type(element=[], element_index=7, column=7)` → IndexError: list index out of range
- `pandapower/protection/utility_functions.py` — `calc_line_intersection(m1=0, b1=0, m2=0, b2=0)` → ZeroDivisionError: division by zero
- `pandapower/pypower/util.py` — `sub2ind(shape=[], I=7, J=7, row_major=7)` → IndexError: list index out of range
- `pandapower/timeseries/run_time_series.py` — `cleanup(net=0, ts_variables={4: 2})` → KeyError: 'recycle_options'
- `pandapower/create/_utils.py` — `_check_element(net=[3, 7], element_index=1, element=7)` → IndexError: list index out of range
- `pandapower/pf/run_bfswpf.py` — `_get_options(options={})` → KeyError: 'enforce_q_lims'
- `pandapower/results.py` — `_get_costs(net=0, ppc={4: 2})` → KeyError: 'obj'
- `pandapower/results.py` — `_ppci_other_to_ppc(result={}, ppc={}, mode=b   )` → KeyError: 'success'
