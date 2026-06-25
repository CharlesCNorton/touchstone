# Bugs

Crashes found by `touchstone scan` in third-party code.

## TheAlgorithms/Python

- `maths/modular_division.py` — `greatest_common_divisor(5, 0)` → ZeroDivisionError: integer modulo by zero
- `maths/interquartile_range.py` — `interquartile_range([5])` → IndexError: list index out of range
- `maths/perfect_square.py` — `perfect_square(-5)` → ValueError: math domain error
- `maths/least_common_multiple.py` — `least_common_multiple_slow(0, 5)` → ZeroDivisionError: integer modulo by zero
- `maths/binary_multiplication.py` — `binary_mod_multiply(1, 1, 0)` → ZeroDivisionError: integer modulo by zero
- `maths/modular_exponential.py` — `modular_exponential(2, 3, 0)` → ZeroDivisionError: integer modulo by zero
- `maths/area.py` — `area_triangle_three_sides` near-degenerate float triangle → ValueError: math domain error
- `maths/greatest_common_divisor.py` — module import (line 76 `except IndexError, UnboundLocalError, ValueError:`) → SyntaxError: multiple exception types must be parenthesized

## huggingface/huggingface_hub

- `src/huggingface_hub/utils/_paths.py` — `filter_repo_objects(["a.txt"], allow_patterns=[""])` → IndexError: string index out of range

## huggingface/transformers

- `src/transformers/integrations/finegrained_fp8.py` — `_cdiv(1, 0)` → ZeroDivisionError: integer division or modulo by zero
- `src/transformers/audio_utils.py` — `window_function(window_length=-1, frame_length=-1)` → ValueError: negative dimensions are not allowed

## huggingface/trl

- `trl/trainer/utils.py` — `compute_mfu(100e9, 1000.0, 0)` → ZeroDivisionError: float division by zero

## huggingface/pytorch-image-models

- `timm/utils/metrics.py` — `AverageMeter().update(1.0, n=0)` → ZeroDivisionError: float division by zero

## mistralai/mistral-common

- `src/mistral_common/tokens/tokenizers/audio.py` — `AudioConfig(sampling_rate=1, frame_rate=2.0)` padding path (`raw_audio_length_per_tok == 0`) → ZeroDivisionError: integer modulo by zero

## lucidrains/vit-pytorch

- `vit_pytorch/pit.py` — `conv_output_size(224, 16, 0)` → ZeroDivisionError: division by zero
- `vit_pytorch/t2t.py` — `conv_output_size(224, 16, 0, 0)` → ZeroDivisionError: division by zero

## networkx/networkx

- `networkx/readwrite/graph6.py` — `from_graph6_bytes(b"")` → IndexError: list index out of range

## benhamner/Metrics

- `Python/ml_metrics/elementwise.py` — `ce([], [])` → ZeroDivisionError: division by zero

## python/cpython

- `Lib/colorsys.py` — `rgb_to_hsv(-1, 0, -2)` → ZeroDivisionError: division by zero
- `Lib/turtle.py` — `TNavigator().degrees(0)` → ZeroDivisionError: division by zero
