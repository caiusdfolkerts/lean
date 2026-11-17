"""Fail closed unless each project's latest main build verifies current inputs."""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def git(*args):
    return subprocess.check_output(['git', *args])


def fingerprint(ref, project):
    # Match the per-project workflow filters, including the build recipe itself.
    tree = git('ls-tree', '-rz', ref, '--', project,
               '.github/workflows/build-project.yml',
               f'.github/workflows/project-{project}.yml')
    entries = []
    for entry in tree.split(b'\0'):
        if not entry:
            continue
        path = entry.split(b'\t', 1)[1].decode()
        if path.startswith(project + '/') and path.endswith(('.md', '.pdf')):
            continue
        entries.append(entry)
    return hashlib.sha256(b'\0'.join(entries)).hexdigest()


def latest_main_run(runs):
    eligible = [run for run in runs
                if run['head_branch'] == 'main'
                and run['event'] in ('push', 'workflow_dispatch')]
    return max(eligible, key=lambda run: run['id'], default=None)


def verdict(run, current, built):
    if run is None:
        return 'No build yet'
    if run['status'] != 'completed':
        return 'Build ' + run['status']
    if run['conclusion'] != 'success':
        return 'Build ' + str(run['conclusion'])
    if current != built:
        return 'Current build inputs have not passed'
    return 'Passed'


def check(project, repository):
    endpoint = (f'repos/{repository}/actions/workflows/project-{project}.yml/runs'
                '?branch=main&per_page=100')
    data = json.loads(subprocess.check_output(['gh', 'api', endpoint]))
    run = latest_main_run(data['workflow_runs'])
    current = fingerprint('HEAD', project)
    built = fingerprint(run['head_sha'], project) if run else None
    return project, verdict(run, current, built), run['html_url'] if run else ''


def main():
    script = Path(__file__).with_name('discover_projects.py')
    projects = json.loads(subprocess.check_output([sys.executable, str(script)]))['project']
    # Check that new projects cannot silently be left out of the status badge.
    for project in projects:
        if not Path(f'.github/workflows/project-{project}.yml').is_file():
            raise RuntimeError(f'Missing project workflow: {project}')
    repository = os.environ['GITHUB_REPOSITORY']
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda project: check(project, repository), projects))
    lines = ['| Project | Latest build |', '| --- | --- |']
    for project, status, url in results:
        print(f'{project}: {status}')
        lines.append(f'| {project} | [{status}]({url}) |' if url else f'| {project} | {status} |')
    if 'GITHUB_STEP_SUMMARY' in os.environ:
        Path(os.environ['GITHUB_STEP_SUMMARY']).write_text('\n'.join(lines) + '\n')
    return 0 if all(status == 'Passed' for _, status, _ in results) else 1


if __name__ == '__main__':
    sys.exit(main())
