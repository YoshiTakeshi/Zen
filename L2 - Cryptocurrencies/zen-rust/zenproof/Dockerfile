# Zen testnet node: one image for any machine (linux/amd64 and linux/arm64: Windows and Intel Macs through Docker Desktop, Apple Silicon,
# Raspberry Pi, servers, clusters).
#   docker run -d --name zen -p 127.0.0.1:18440-18462:18440-18462 -v zen-data:/data ghcr.io/OWNER/zen:latest
FROM rust:1-bookworm AS build
ENV RUSTC_BOOTSTRAP=1 CARGO_TERM_COLOR=never
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY .cargo .cargo
COPY src src
RUN cargo build --release --locked && strip target/release/zenproof

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates tini && rm -rf /var/lib/apt/lists/* \
 && useradd --system --uid 10001 --home /data --shell /usr/sbin/nologin zen && mkdir -p /data && chown zen /data
COPY --from=build /src/target/release/zenproof /usr/local/bin/zenproof
COPY docker/entrypoint.sh /usr/local/bin/zen-entrypoint
RUN chmod 0755 /usr/local/bin/zen-entrypoint
USER zen
WORKDIR /data
VOLUME /data
# p2p 18440-18442 (Yen, Ken, Jen), Stratum 18450-18452, API / explorer 18460-18462
EXPOSE 18440 18441 18442 18450 18451 18452 18460 18461 18462
# inside a container the node listens on the container's own address; publish the ports on the host's loopback unless you mean to open them
ENV ZEN_BIND=0.0.0.0 ZEN_API_BIND=0.0.0.0 ZEN_API_BIND_ANY=1 ZEN_AUTOMINE=1 ZEN_BLOCK_SECS=20
HEALTHCHECK --interval=30s --timeout=5s --start-period=60s --retries=3 CMD ["/usr/local/bin/zen-entrypoint", "healthcheck"]
ENTRYPOINT ["/usr/bin/tini", "--", "/usr/local/bin/zen-entrypoint"]
CMD ["testnet"]
