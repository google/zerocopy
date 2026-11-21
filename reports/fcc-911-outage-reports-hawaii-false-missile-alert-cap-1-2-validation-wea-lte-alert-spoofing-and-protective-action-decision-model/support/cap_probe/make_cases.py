#!/usr/bin/env python3
"""Write the CAP 1.2 conformance-probe corpus (one .xml file per case).

Usage: python3 make_cases.py <out dir>
Each case is a small CAP 1.2 alert that differs from a valid baseline in one
respect. Expected spec status is recorded in cases.tsv next to the files;
"spec" cites the OASIS CAP 1.2 element rule the case exercises.
All content is synthetic.
"""
import os, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)

def alert(identifier='EX-0001', sent='2018-01-13T08:07:00-10:00', status='Actual',
          msgType='Alert', scope='Public', extra_head='', infos=None, raw_head=None):
    head = raw_head if raw_head is not None else (
        f'<identifier>{identifier}</identifier>'
        f'<sender>alerts@example.org</sender>'
        f'<sent>{sent}</sent><status>{status}</status>'
        f'<msgType>{msgType}</msgType><scope>{scope}</scope>{extra_head}')
    if infos is None:
        infos = [info()]
    return ('<?xml version="1.0" encoding="UTF-8"?>\n'
            '<alert xmlns="urn:oasis:names:tc:emergency:cap:1.2">'
            + head + ''.join(infos) + '</alert>\n')

POLY_OK = '21.2,-158.3 21.2,-157.6 21.6,-157.6 21.6,-158.3 21.2,-158.3'

def info(language=None, headline='Test headline', description='Test description',
         area=None, extra=''):
    lang = '' if language is None else f'<language>{language}</language>'
    if area is None:
        area = f'<area><areaDesc>Example area</areaDesc><polygon>{POLY_OK}</polygon></area>'
    return (f'<info>{lang}<category>Safety</category><event>Test event</event>'
            f'<urgency>Immediate</urgency><severity>Extreme</severity><certainty>Observed</certainty>'
            f'{extra}<headline>{headline}</headline><description>{description}</description>{area}</info>')

def area(poly=None, circle=None, alt=None, ceil=None):
    s = '<area><areaDesc>Example area</areaDesc>'
    if poly is not None:
        s += f'<polygon>{poly}</polygon>'
    if circle is not None:
        s += f'<circle>{circle}</circle>'
    if alt is not None:
        s += f'<altitude>{alt}</altitude>'
    if ceil is not None:
        s += f'<ceiling>{ceil}</ceiling>'
    return s + '</area>'

REF = 'alerts@example.org,EX-0000,2018-01-13T07:00:00-10:00'
CASES = [
    # name, xml, spec-expected
    ('c01_valid_baseline', alert(), 'valid'),
    ('c02_missing_identifier', alert(raw_head='<sender>alerts@example.org</sender><sent>2018-01-13T08:07:00-10:00</sent><status>Actual</status><msgType>Alert</msgType><scope>Public</scope>'), 'invalid: identifier REQUIRED'),
    ('c03_sent_without_tz', alert(sent='2018-01-13T08:07:00'), 'invalid: sent must carry a time zone offset'),
    ('c04_sent_Z_suffix', alert(sent='2018-01-13T18:07:00Z'), 'invalid: CAP 1.2 says alphabetic time zone designators such as Z MUST NOT be used'),
    ('c05_update_without_references', alert(msgType='Update'), 'valid per core spec (references optional); profiles may require'),
    ('c06_cancel_with_references', alert(msgType='Cancel', extra_head=f'<references>{REF}</references>'), 'valid'),
    ('c07_circular_reference', alert(msgType='Cancel', extra_head='<references>alerts@example.org,EX-0001,2018-01-13T08:07:00-10:00</references>'), 'semantically inconsistent: references itself'),
    ('c08_postdated_reference', alert(msgType='Update', extra_head='<references>alerts@example.org,EX-0000,2018-01-13T09:00:00-10:00</references>'), 'semantically inconsistent: referenced message sent later'),
    ('c09_restriction_with_public_scope', alert(extra_head='<restriction>internal</restriction>'), 'inconsistent: restriction is used when scope is Restricted'),
    ('c10_restricted_scope_no_restriction', alert(scope='Restricted'), 'inconsistent: restriction should be present when scope is Restricted'),
    ('c11_private_scope_no_addresses', alert(scope='Private'), 'invalid: addresses REQUIRED when scope is Private'),
    ('c12_polygon_not_closed', alert(infos=[info(area=area(poly='21.2,-158.3 21.2,-157.6 21.6,-157.6 21.6,-158.3'))]), 'invalid: first and last pairs must be equal'),
    ('c13_polygon_three_points', alert(infos=[info(area=area(poly='21.2,-158.3 21.2,-157.6 21.2,-158.3'))]), 'invalid: at least four coordinate pairs'),
    ('c14_polygon_bowtie', alert(infos=[info(area=area(poly='21.2,-158.3 21.6,-157.6 21.2,-157.6 21.6,-158.3 21.2,-158.3'))]), 'not ruled out by text; self-intersecting'),
    ('c15_polygon_antimeridian', alert(infos=[info(area=area(poly='-17.0,179.0 -17.0,-179.0 -16.0,-179.0 -16.0,179.0 -17.0,179.0'))]), 'valid small box crossing 180 degrees'),
    ('c16_circle_ok', alert(infos=[info(area=area(circle='21.3,-157.8 10.0'))]), 'valid'),
    ('c17_ceiling_without_altitude', alert(infos=[info(area=area(poly=POLY_OK, ceil='100'))]), 'invalid: ceiling MAY only be used with altitude'),
    ('c18_altitude_above_ceiling', alert(infos=[info(area=area(poly=POLY_OK, alt='200', ceil='100'))]), 'inconsistent: altitude above ceiling'),
    ('c19_empty_language', alert(infos=[info(language='')]), 'invalid: language must be an RFC 3066 code'),
    ('c20_whitespace_language', alert(infos=[info(language=' ')]), 'invalid: language must be an RFC 3066 code'),
    ('c21_bad_language', alert(infos=[info(language='english_US')]), 'invalid: language must be an RFC 3066 code'),
    ('c22_same_text_two_languages', alert(infos=[info(language='en-US', headline='Same'), info(language='es-US', headline='Same')]), 'suspicious: identical text under different languages'),
    ('c23_same_text_same_language', alert(infos=[info(language='en-US', headline='Same'), info(language='en-GB', headline='Same')]), 'valid'),
    ('c24_html_in_description', alert(infos=[info(description='&lt;b&gt;WATCH OUT&lt;/b&gt;')]), 'text should be plain'),
    ('c25_expires_before_effective', alert(infos=[info(extra='<effective>2018-01-13T09:00:00-10:00</effective><expires>2018-01-13T08:00:00-10:00</expires>')]), 'semantically inconsistent: expires before effective'),
    ('c26_actual_status_exercise_text', alert(infos=[info(headline='EXERCISE EXERCISE EXERCISE', description='This is a drill message body')]), 'schema-valid; status contradicts text'),
    ('c27_exercise_status_live_text', alert(status='Exercise', infos=[info(headline='THIS IS NOT A DRILL')]), 'schema-valid; status contradicts text'),
    ('c28_no_info', alert(infos=[]), 'valid per core spec (info optional)'),
    ('c29_bad_status_value', alert(status='Drill'), 'invalid: status enumeration'),
]
with open(os.path.join(out, 'cases.tsv'), 'w') as tsv:
    tsv.write('case\tspec_expectation\n')
    for name, xml, exp in CASES:
        with open(os.path.join(out, name + '.xml'), 'w') as fh:
            fh.write(xml)
        tsv.write(f'{name}\t{exp}\n')
print(f'wrote {len(CASES)} cases to {out}')
