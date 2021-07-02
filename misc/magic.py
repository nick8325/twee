import re
import tensorflow as tf
from tensorflow.keras import *
from tensorflow.keras.layers import *
from tensorflow.keras.metrics import *
from numpy.random import shuffle
from pprint import pprint
from collections import namedtuple
from glob import glob

dim = 30

model = Sequential()
model.add(Bidirectional(LSTM(dim, dropout = 0.1, input_shape=(1, None), return_sequences = True)))
model.add(Bidirectional(LSTM(dim, dropout = 0.1, return_sequences = True)))
model.add(Bidirectional(LSTM(dim, dropout = 0.1)))
model.add(Dense(1))
model.add(Activation('sigmoid'))
model.compile(loss='binary_crossentropy', optimizer='adam',
        metrics=[BinaryAccuracy(), Precision(), Recall()])

problem = namedtuple('problem', ['vars', 'funcs', 'goal', 'axioms', 'rules'])

def read_problem(file):
    vars = None
    funcs = None
    goal = None
    axioms = []
    rules = []

    for line in open(file):
        line = line[:-1]
        prefix, rest = line.split(",", 1)
        if prefix == "vars":
            vars = rest.replace("[","").replace("]","").split(",")
        elif prefix == "funcs":
            funcs_list = rest.replace(" ", "").replace("[","").replace("]","").split(",")
            funcs = {func: list(map(int, info)) for func_arity in funcs_list for func, *info in [func_arity.split("/")]}
        elif prefix == "goal":
            goal = rest
        elif prefix == "axiom":
            axioms.append(rest)
        elif prefix == "false":
            rules.append((rest, False))
        elif prefix == "true":
            rules.append((rest, True))
        else:
            raise ValueError(prefix)

    return problem(vars, funcs, goal, axioms, rules)

problems = [read_problem(file) for file in glob("traces-out/modRNG*")]
rules = [(rule, used, problem) for problem in problems if problem.goal is not None for rule, used in problem.rules]
used = [(rule, problem) for rule, used, problem in rules if used]
unused = [(rule, problem) for rule, used, problem in rules if not used]
print(len(used), "used,", len(unused), "unused")

shuffle(unused)

def mask(info = [-1, -1, -1]):
    return tf.concat([tf.constant(list(map(float, info))), tf.random.uniform([dim])], 0)

static = [x for x in "!;(,)=X"]
static_emb = {x: mask() for x in static}

def tokenise(s):
    return [x for x in re.split("([ !;(),=])", s) if x.strip()]

def embed(emb, s):
    return tf.stack([lookup(x, emb) for x in tokenise(s)])

def lookup(x, emb):
    result = static_emb.get(x, emb.get(x))
    if result is None:
        raise ValueError(x)
    else:
        return result

def train_on(rule, problem, used):
    print(used, rule)
    if used:
        weight = 1 #2
    else:
        weight = 1
    emb = {x: mask(info) for x, info in problem.funcs.items()}
    for x in problem.vars:
        emb[x] = static_emb['X'] + mask()
    batch = tf.expand_dims(embed(emb, ";".join([problem.goal, *problem.axioms, "!" + rule])), 0)
    info = model.train_on_batch(batch,
            tf.constant([[float(used)]]), return_dict=True,
            reset_metrics=reset_metrics, sample_weight=[float(weight)])
    #info['prediction'] = model(batch)[(0,0)].numpy()
    print(info)
    print()

used_reservoir = []
for epoch in range(10):
    print("Epoch " + str(epoch) + "!!!")
    reset_metrics = True
    for rule, problem in unused:
        train_on(rule, problem, False)

        for _ in range(1):
            if not used_reservoir:
                used_reservoir = used
                shuffle(used_reservoir)
            rule, problem = used_reservoir[0]
            train_on(rule, problem, True)
            used_reservoir = used_reservoir[1:]

        reset_metrics = False
