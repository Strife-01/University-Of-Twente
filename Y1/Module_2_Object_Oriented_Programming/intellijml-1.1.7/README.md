# IntelliJML

The Java Modeling Language (JML) is a specification language that is used to specify intended
behavior of Java programs. This project aims to be an easy-to-use plugin for IntelliJ IDEA that
provides support for modern Java versions. Features such as syntax, semantic, and type checking, as
well as syntax highlighting and code completion are provided to aid users in writing JML
specifications in a convenient manner.

## Installation

The installable plugin file (a .jar file) can be found in the [releases section](https://gitlab.utwente.nl/fmt/intellijml/-/releases).

An installation guide can be found [here](docs/Installation_Guide.pdf)

## Build from source

1. Import the source code into IntelliJ IDEA.

2. Open the Gradle tab and reload the Gradle project.

3. Then go to the Gradle **tasks > build > jar**

4. The generated .jar file can then be found in the directory **build/libs**

**Note that gradle must be run with JDK 11 for a successful build**

## Developer Guide

A guide for the plugin architecture can be found [here](docs/Maintainers_Guide.pdf)

## Running tests

A guide for running tests can be found [here](docs/Maintainers_Guide.pdf) in chapter 8.