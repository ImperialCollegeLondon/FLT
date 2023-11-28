import os
import shutil
import subprocess
from pathlib import Path
from invoke import run, task

from blueprint.tasks import web, bp, print_bp, serve

ROOT = Path(__file__).parent
BP_DIR = ROOT/'blueprint'

@task
def copy(ctx):
    shutil.rmtree(ROOT/'docs'/'blueprint', ignore_errors=True)
    shutil.copytree(ROOT/'blueprint'/'web', ROOT/'docs'/'blueprint')
    shutil.copy2(ROOT/'blueprint'/'print'/'print.pdf', ROOT/'docs'/'blueprint.pdf')

@task(bp, web, copy)
def all(ctx):
    pass

@task(web)
def html(ctx):
    shutil.rmtree(ROOT/'docs'/'blueprint', ignore_errors=True)
    shutil.copytree(ROOT/'blueprint'/'web', ROOT/'docs'/'blueprint')

@task(bp, web)
def dev(ctx):
    """
    Serve the blueprint website, rebuild PDF and the website on file changes
    """

    from watchfiles import run_process, DefaultFilter

    def callback(changes):
        print('Changes detected:', changes)
        bp(ctx)
        web(ctx)
    
    run_process(BP_DIR/'src', target='inv serve', callback=callback,
        watch_filter=DefaultFilter(
            ignore_entity_patterns=(
                '.*\.aux$',
                '.*\.log$',
                '.*\.fls$',
                '.*\.fdb_latexmk$',
                '.*\.bbl$',
                '.*\.paux$',
                '.*\.pdf$',
                '.*\.out$',
                '.*\.blg$',
                '.*\.synctex.*$',
            )
        ))