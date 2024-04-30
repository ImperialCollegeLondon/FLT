import os
import random
from pathlib import Path
import http.server
import socketserver

from invoke import run, task

BP_DIR = Path(__file__).parent

@task
def print_bp(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
    os.chdir(cwd)

@task
def bp(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
    run('cd src && xelatex -output-directory=../print print.tex')
    run('cp print/print.bbl src/web.bbl')
    os.chdir(cwd)

@task
def bptt(ctx):
    """
    Build the blueprint PDF file with tectonic and prepare src/web.bbl for task `web`

    NOTE: install tectonic by running `curl --proto '=https' --tlsv1.2 -fsSL https://drop-sh.fullyjustified.net |sh` in
    `~/.local/bin/`
    """

    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && tectonic -Z shell-escape-cwd=. --keep-intermediates --outdir ../print print.tex')
    # run('cp print/print.bbl src/web.bbl')
    os.chdir(cwd)

@task
def web(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR/'src')
    run('plastex -c plastex.cfg web.tex')
    os.chdir(cwd)

@task
def serve(ctx, port=8080, random_port=False):
    """
    Serve the blueprint website assuming the blueprint website is already built
    """

    class MyTCPServer(socketserver.TCPServer):
        def server_bind(self):
            import socket
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.socket.bind(self.server_address)

    cwd = os.getcwd()
    os.chdir(BP_DIR/'web')

    if random_port:
        port = random.randint(8000, 8100)

    Handler = http.server.SimpleHTTPRequestHandler
    httpd = MyTCPServer(('', port), Handler)

    try:
        (ip, port) = httpd.server_address
        ip = ip or 'localhost'
        print(f'Serving http://{ip}:{port}/ ...')
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    httpd.server_close()

    os.chdir(cwd)
