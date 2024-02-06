from importlib.metadata import entry_points
import setuptools

long_description = open("README.md").read()

setuptools.setup(
    name="proof-mouse",
    version="0.6",
    author="Raghav Malik",
    author_email="malik22@purdue.edu",
    description="Proof Mouse proof checker",
    long_description=long_description,
    url="https://github.com/raghav198/proof-mouse",
    license="MIT",
    packages=["."],
    install_requires=["pyparsing==3.0.9"],
    entry_points={"console_scripts": ["mouse=mouse:main"]},
)
