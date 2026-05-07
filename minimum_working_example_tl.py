import construction_helpers as ch # Needed for @ auto-alignment
import data_structure.Category as cat
import data_structure.Numeric as nm
import data_structure.Operators as ops
import data_structure.Term as fd
import display as dpl
import websocket_transfer.websockets_transfer as wst

import subprocess
import asyncio
import socket
import sys

from typing import Callable, Any, Literal
from data_structure.TensorDSL import TL, axes, norm_axis, relu, softmax

commands: dict[str, Callable[[], Any]] = {}

def attach_command(name: str):
    def name_wrapper(func):
        commands[name] = func
        return func
    return name_wrapper


####################
## MATRIX MULTIPLY ##
####################

# Demonstrates the simplest TensorEquation: Y[i,j] = W[i,k] X[k,j].
# The shared k axis object marks the contracted index; i and j are retained.

def matmul():
    tl = TL()
    i, j, k = axes('i j k')
    tl.Y[i, j] = tl.W[i, k] * tl.X[k, j]
    return tl.bc_signature()

@attach_command('Matrix Multiply')
async def render_matmul():
    print('Matrix Multiply')
    m = matmul()
    dpl.print_category(m)
    await wst.send_term(m)


##########################
## ATTENTION QK MATMUL  ##
##########################

# A single TensorEquation for the QK step of attention with softmax.
# The normalisation axis x is marked with norm_axis (the t. notation from
# tensor logic). softmax() records that normalisation is applied
# over that dimension.
#   Comp[h, q, x.] = softmax(Query[q, h, k] Key[x, h, k])

def attention_qk():
    tl = TL()
    q, h, k = axes('q h k')
    x = norm_axis('x')
    tl.Comp[h, q, x] = softmax(tl.Query[q, h, k] * tl.Key[x, h, k])
    return tl.bc_signature()

@attach_command('Attention QK')
async def render_attention_qk():
    print('Attention QK')
    m = attention_qk()
    dpl.print_category(m)
    await wst.send_term(m)

######################
## ATTENTION CORE   ##
######################

# The two einsum steps of attention are expressed as individual TensorEquations.
# Softmax is folded into the QK equation as its operator; only the causal mask
# remains as an explicit @-composition step between the two einsums.
#
#   QK:  Comp[h, q, x] = softmax(Query[q, h, k] Key[x, h, k])  (contract k)
#   SV:  Out[q, h, k]  = Comp[h, q, x]  Value[x, h, k]         (contract x)

def attention_core():
    tl_qk = TL()
    q1, h1, k1, x1 = axes('q h k x')
    tl_qk.Comp[h1, q1, x1] = softmax(tl_qk.Query[q1, h1, k1] * tl_qk.Key[x1, h1, k1])

    tl_sv = TL()
    q2, h2, k2, x2 = axes('q h k x')
    tl_sv.Out[q2, h2, k2] = tl_sv.Comp[h2, q2, x2] * tl_sv.Value[x2, h2, k2]

    qk   = tl_qk.bc_signature()
    sv   = tl_sv.bc_signature()
    mask = ops.WeightedTriangularLower().template()

    return cat.Block.template(
        qk @ mask @ sv,
        title='Attention Core',
        fill_color='#C5BEDF'
    )

@attach_command('Attention Core')
async def render_attention_core():
    print('Attention Core')
    m = attention_core()
    dpl.print_category(m)
    await wst.send_term(m)


###########
## FFN   ##
###########

# TensorProgram with two equations expresses the full FFN in tensor logic
# notation. TensorProgram.to_morphism() unifies the Hidden axes across the
# two equations via Context before calling bc_signature() on each.
#
#   Hidden[p, d_ff] = relu( W_in[d_ff, d]   X[p, d]      )  (contract d)
#   Output[p, d]    =       W_out[d, d_ff]  Hidden[p, d_ff]  (contract d_ff)

def ffn():
    tl = TL()
    p1, d1, d_ff1 = axes('p d d_{ff}')
    tl.Hidden[p1, d_ff1] = relu(tl.W_in[d_ff1, d1] * tl.X[p1, d1])

    p2, d2, d_ff2 = axes('p d d_{ff}')
    tl.Output[p2, d2] = tl.W_out[d2, d_ff2] * tl.Hidden[p2, d_ff2]

    return cat.Block.template(
        tl.to_program().to_morphism(),
        title='Feed Forward',
        fill_color='#C1E8F7'
    )

@attach_command('FFN')
async def render_ffn():
    print('FFN')
    m = ffn()
    dpl.print_category(m)
    await wst.send_term(m)


#############################
## ATTENTION MATMUL CHAIN  ##
#############################

# Both attention einsums in a single TensorProgram. Without softmax/mask,
# the two steps compose directly: TensorProgram.to_morphism() unifies the
# Comp axes produced by eq_qk with those consumed by eq_sv.
#
#   Comp[h, q, x]  = Query[q, h, k] Key[x, h, k]    (contract k)
#   Out[q, h, k]   = Comp[h, q, x]  Value[x, h, k]  (contract x)

def attention_chain():
    tl = TL()
    q1, h1, k1, x1 = axes('q h k x')
    tl.Comp[h1, q1, x1] = tl.Query[q1, h1, k1] * tl.Key[x1, h1, k1]

    q2, h2, k2, x2 = axes('q h k x')
    tl.Out[q2, h2, k2] = tl.Comp[h2, q2, x2] * tl.Value[x2, h2, k2]

    return cat.Block.template(
        tl.to_program().to_morphism(),
        title='Attention Matmul Chain',
        fill_color='#C5BEDF'
    )

@attach_command('Attention Matmul Chain')
async def render_attention_chain():
    print('Attention Matmul Chain')
    m = attention_chain()
    dpl.print_category(m)
    await wst.send_term(m)


#################
## TRANSFORMER ##
#################

# Full transformer: embedding and aggregator are unchanged (outside tensor
# logic scope — Embedding is selection not contraction, aggregator uses
# Natural datatype). The attention core and FFN layers are TensorLogic-based.

def res(target: cat.BroadcastedCategory):
    return cat.Block.template(
        (0, 0) @ target @ ops.AdditionOp.template() @ ops.Normalize.template(),
        title='Add \\& Norm',
        fill_color='#F1F4C1'
    )

def attention_layer():
    _attention_core = attention_core()
    Lq = ops.Linear.template(('m',), 2, 'q')
    Lk = ops.Linear.template(('m',), 2, 'k')
    Lv = ops.Linear.template(('m',), 2, 'v')
    Lo = ops.Linear.template(2, ('m',), 'o')
    return (Lq * Lk * Lv) @ _attention_core @ Lo

def transformer_core():
    _attention_layer = attention_layer()
    _ffn_layer = ffn()
    return cat.Block.template(
        res(_attention_layer) @ res(_ffn_layer),
        title='Transformer Layer',
        fill_color='#F3F3F4',
        repetition=nm.Integer(6)
    )

def transformer():
    vocab_size = fd.DynamicName('v', settings=fd.DynamicNameSettings(overline=True))
    embedding = cat.Block.template(
        ops.Embedding.template(vocab_size),
        title='Embedding',
        fill_color='#FCE0E1'
    )
    aggregator = cat.Block.template(
        ops.Linear.template(1, (vocab_size,)) @ ops.SoftMax.template(),
        title='Aggregator',
        fill_color='#DBDFEF'
    )
    return embedding @ transformer_core() @ aggregator

@attach_command('Transformer')
async def render_transformer():
    print('Transformer')
    _transformer = transformer()
    dpl.print_category(_transformer) # type: ignore
    await wst.send_term(_transformer)


def print_options():
    print('Available commands:')
    for i, command in enumerate(commands):
        print(f'({i}) {command}')
    print('(q) Quit')

async def ask_input() -> None | Literal['Quit']:
    while True:
        print_options()
        choice = input('Enter command number, or q to quit: ')
        if choice.lower() == 'q':
            return 'Quit'
        try:
            choice = int(choice)
            command_name = list(commands.keys())[choice]
            await commands[command_name]()
        except (ValueError, IndexError):
            print('Invalid choice. Please enter a valid command number, or q to quit.')

if __name__ == '__main__':
    def server_is_running(host: str = '127.0.0.1', port: int = 8765) -> bool:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.settimeout(0.5)
            return sock.connect_ex((host, port)) == 0

    started_server_here = False
    server = None
    if server_is_running():
        print('Using existing server at ws://localhost:8765')
    else:
        server = subprocess.Popen([sys.executable, 'run_server.py'])
        started_server_here = True
        print('Server started.')

    while True:
        command = asyncio.run(ask_input())
        if command == 'Quit':
            print('Exiting.')
            if started_server_here and server is not None:
                server.kill()
            break
