#!/usr/bin/env python3

import sys
import re
import configparser

# TODO: for Python 3.5 or higher: z = {**x, **y}
def merge_two_dicts(x, y):
    z = dict(x)
    z.update(y)
    return z

def subst(text, key, val):
    return text.replace('{' + key.upper() + '}', val)

def safe_get(config, section):
    if section in config:
        return config[section]
    else:
        return {}

def inherit_get(config, section):
    if not section:
        return safe_get(config, 'DEFAULT')
    else:
        parent = inherit_get(config, '-'.join(section.split('-')[:-1]))
        current = safe_get(config, section)
        merged = merge_two_dicts(parent, current) # TODO: for Python 3.5 or higher: {**parent, **current}
        for key in list(merged.keys()):
            if key.startswith('+'):
                merged[key[1:]] += merged[key]
                del merged[key]
        return merged

def gen(template, spec_ini, pgm_ini, name):
    spec_config = configparser.ConfigParser(comment_prefixes=(';'))
    spec_config.read(spec_ini)
    pgm_config = configparser.ConfigParser(comment_prefixes=(';'))
    pgm_config.read(pgm_ini)
    genspec = template
    for config in [ inherit_get(spec_config, name)
                  , {'module': name.upper()}
                  , pgm_config['DEFAULT']
                  ]:
        for key in config:
            genspec = subst(genspec, key, config[key].strip())
    print(genspec)

if __name__ == '__main__':
    if len(sys.argv) != 5:
        print("usage: <cmd> <template> <spec_ini> <pgm_ini> <name>")
        sys.exit(1)
    template = open(sys.argv[1], "r").read()
    gen(template, sys.argv[2], sys.argv[3], sys.argv[4])
