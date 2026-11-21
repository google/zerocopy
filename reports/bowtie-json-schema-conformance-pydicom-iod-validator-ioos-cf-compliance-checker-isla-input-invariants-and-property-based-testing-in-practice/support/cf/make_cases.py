#!/usr/bin/env python3
"""Generate small netCDF-4 files that probe edge cases of CF metadata checking.

Each file is a minimal, otherwise-plausible CF-1.8 dataset with one deliberate
edge case in variable `v`. Writes into the directory given as argv[1].
"""
import sys, os
import numpy as np
import netCDF4

out = sys.argv[1]
os.makedirs(out, exist_ok=True)

def base(path, vtype='f4', fill=None):
    ds = netCDF4.Dataset(path, 'w', format='NETCDF4')
    ds.Conventions = 'CF-1.8'
    ds.title = 'edge-case probe'
    ds.createDimension('time', 3)
    t = ds.createVariable('time', 'f8', ('time',))
    t.standard_name = 'time'; t.units = 'days since 1970-01-01'; t.calendar = 'standard'; t.axis = 'T'
    t[:] = [0, 1, 2]
    kw = {} if fill is None else {'fill_value': fill}
    v = ds.createVariable('v', vtype, ('time',), **kw)
    return ds, v

cases = {}

def case(name):
    def deco(f):
        cases[name] = f
        return f
    return deco

@case('00_baseline')
def _(p):
    ds, v = base(p); v.standard_name = 'air_temperature'; v.units = 'K'; v[:] = [280, 281, 282]; ds.close()

@case('01_fill_inside_valid_min_only')
def _(p):
    # _FillValue lies inside [valid_min, +inf); only one bound is given.
    ds, v = base(p, fill=np.float32(5.0)); v.standard_name = 'air_temperature'; v.units = 'K'
    v.valid_min = np.float32(0.0); v[:] = [280, 281, 282]; ds.close()

@case('02_fill_inside_valid_range')
def _(p):
    ds, v = base(p, fill=np.float32(5.0)); v.standard_name = 'air_temperature'; v.units = 'K'
    v.valid_range = np.array([0, 400], 'f4'); v[:] = [280, 281, 282]; ds.close()

@case('03_valid_range_three_elements')
def _(p):
    ds, v = base(p, fill=np.float32(-999.0)); v.standard_name = 'air_temperature'; v.units = 'K'
    v.valid_range = np.array([0, 400, 500], 'f4'); v[:] = [280, 281, 282]; ds.close()

@case('04_valid_range_nan_bound')
def _(p):
    ds, v = base(p, fill=np.float32(-999.0)); v.standard_name = 'air_temperature'; v.units = 'K'
    v.valid_range = np.array([np.nan, 400], 'f4'); v[:] = [280, 281, 282]; ds.close()

@case('05_fill_nan_with_valid_range')
def _(p):
    ds, v = base(p, fill=np.float32(np.nan)); v.standard_name = 'air_temperature'; v.units = 'K'
    v.valid_range = np.array([0, 400], 'f4'); v[:] = [280, 281, 282]; ds.close()

@case('06_flag_meanings_whitespace_only_empty_values')
def _(p):
    ds, v = base(p, vtype='i1'); v.long_name = 'quality flag'
    v.setncattr('flag_values', np.array([], 'i1'))
    v.flag_meanings = '   '
    v[:] = [0, 0, 0]; ds.close()

@case('07_flag_meanings_whitespace_one_value')
def _(p):
    ds, v = base(p, vtype='i1'); v.long_name = 'quality flag'
    v.flag_values = np.array([1], 'i1'); v.flag_meanings = '   '
    v[:] = [1, 1, 1]; ds.close()

@case('08_units_unparseable')
def _(p):
    ds, v = base(p); v.standard_name = 'air_temperature'; v.units = 'kelvinish'; v[:] = [280, 281, 282]; ds.close()

@case('09_units_incompatible_with_standard_name')
def _(p):
    ds, v = base(p); v.standard_name = 'air_temperature'; v.units = 'm s-1'; v[:] = [280, 281, 282]; ds.close()

@case('10_coordinates_attr_missing_var')
def _(p):
    ds, v = base(p); v.standard_name = 'air_temperature'; v.units = 'K'; v.coordinates = 'lat lon'; v[:] = [280, 281, 282]; ds.close()

@case('11_cell_methods_trailing_garbage')
def _(p):
    ds, v = base(p); v.standard_name = 'air_temperature'; v.units = 'K'; v.cell_methods = 'time: mean ;;; DROP'; v[:] = [280, 281, 282]; ds.close()

@case('12_calendar_unknown')
def _(p):
    ds = netCDF4.Dataset(p, 'w', format='NETCDF4'); ds.Conventions = 'CF-1.8'
    ds.createDimension('time', 3)
    t = ds.createVariable('time', 'f8', ('time',)); t.standard_name = 'time'; t.units = 'days since 1970-01-01'; t.calendar = 'martian'; t.axis = 'T'; t[:] = [0, 1, 2]
    v = ds.createVariable('v', 'f4', ('time',)); v.standard_name = 'air_temperature'; v.units = 'K'; v[:] = [1, 2, 3]; ds.close()

@case('13_time_units_invalid_date')
def _(p):
    ds = netCDF4.Dataset(p, 'w', format='NETCDF4'); ds.Conventions = 'CF-1.8'
    ds.createDimension('time', 3)
    t = ds.createVariable('time', 'f8', ('time',)); t.standard_name = 'time'; t.units = 'days since 1970-13-45'; t.calendar = 'standard'; t.axis = 'T'; t[:] = [0, 1, 2]
    v = ds.createVariable('v', 'f4', ('time',)); v.standard_name = 'air_temperature'; v.units = 'K'; v[:] = [1, 2, 3]; ds.close()

@case('14_no_conventions_attr')
def _(p):
    ds, v = base(p); ds.delncattr('Conventions'); v.standard_name = 'air_temperature'; v.units = 'K'; v[:] = [280, 281, 282]; ds.close()

@case('15_standard_name_unknown')
def _(p):
    ds, v = base(p); v.standard_name = 'air_temperature_of_mars'; v.units = 'K'; v[:] = [280, 281, 282]; ds.close()

@case('16_time_values_nonmonotonic_nan')
def _(p):
    ds = netCDF4.Dataset(p, 'w', format='NETCDF4'); ds.Conventions = 'CF-1.8'
    ds.createDimension('time', 3)
    t = ds.createVariable('time', 'f8', ('time',), fill_value=False); t.standard_name = 'time'; t.units = 'days since 1970-01-01'; t.calendar = 'standard'; t.axis = 'T'
    t[:] = [0.0, np.nan, 2.0]
    v = ds.createVariable('v', 'f4', ('time',)); v.standard_name = 'air_temperature'; v.units = 'K'; v[:] = [1, 2, 3]; ds.close()

for name, f in cases.items():
    p = os.path.join(out, name + '.nc')
    try:
        f(p); print('wrote', p)
    except Exception as e:
        print('FAILED to write', name, type(e).__name__, e)
