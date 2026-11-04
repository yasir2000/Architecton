FROM rust:bookworm AS build
WORKDIR /work
COPY backend ./backend
RUN cargo build --release --manifest-path backend/Cargo.toml

FROM debian:bookworm-slim
RUN useradd --create-home --uid 10001 app && mkdir /data && chown app:app /data
COPY --from=build /work/backend/target/release/driverpass-poc /usr/local/bin/driverpass-poc
USER app
ENV DATABASE_PATH=/data/driverpass.db PORT=3000 HOST=0.0.0.0
EXPOSE 3000
CMD ["/usr/local/bin/driverpass-poc"]
