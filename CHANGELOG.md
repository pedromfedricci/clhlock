# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.1] - 2024-11-04

### Added
- Improve documentation about `MutexNode` ownership under locking APIs ([`4fd44b6`])

[`4fd44b6`]: https://github.com/pedromfedricci/clhlock/commit/4fd44b61cfac89e20e29b2460477cc4582ea8f48

## [0.2.0] - 2024-10-31

### Added
- Add new `Mutex::lock`, `Mutex::lock_with_then` and `Mutex::lock_then` ([#5])
- Add semver check workflow

### Changed
- **BREAKING**: Rename `Mutex::lock` to `Mutex::lock_with` ([#5])
- **BREAKING**: Rename `Mutex::lock_with` to `Mutex::lock_then` ([#5])
- **BREAKING**: Consume nodes on `Mutex` locking methods  ([#4])
- Add Send/sync for node and guard
- Update categories and keywords


### Fixed
- Improve test coverage
- Improve relax testing

### Removed
- **BREAKING**: Remove thread local support ([#3])

[#5]: https://github.com/pedromfedricci/clhlock/pull/5
[#4]: https://github.com/pedromfedricci/clhlock/pull/4
[#3]: https://github.com/pedromfedricci/clhlock/pull/3

## [0.1.0] - 2024-08-28 [YANKED]

### Added
- Add test coverage
- Add nextest config

[unreleased]: https://github.com/pedromfedricci/clhlock/compare/v0.2.1..HEAD
