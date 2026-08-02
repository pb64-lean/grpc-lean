#!/bin/bash
# Stress test for UserService gRPC server

set -e

HOST="localhost:50051"
DURATION=10  # seconds
CONCURRENCY=10  # parallel workers
PROTO_ARGS=(-import-path proto -proto user_service.proto)

echo "=============================================="
echo "UserService gRPC Stress Test"
echo "=============================================="
echo "Host: $HOST"
echo "Duration: ${DURATION}s"
echo "Concurrency: $CONCURRENCY workers"
echo ""

# Check if server is reachable
if ! grpcurl -plaintext $HOST list > /dev/null 2>&1; then
    echo "ERROR: Server not reachable at $HOST"
    exit 1
fi

# Function to run requests in a loop
run_worker() {
    local worker_id=$1
    local end_time=$2
    local count=0
    local errors=0

    while [ $(date +%s) -lt $end_time ]; do
        # Mix of different RPC calls
        case $((count % 4)) in
            0)
                # GetUser
                if grpcurl -plaintext "${PROTO_ARGS[@]}" -d '{"user_id": 1}' $HOST userservice.UserService/GetUser > /dev/null 2>&1; then
                    ((count++))
                else
                    ((errors++))
                fi
                ;;
            1)
                # ListUsers
                if grpcurl -plaintext "${PROTO_ARGS[@]}" -d '{"limit": 10}' $HOST userservice.UserService/ListUsers > /dev/null 2>&1; then
                    ((count++))
                else
                    ((errors++))
                fi
                ;;
            2)
                # GetUser (different user)
                if grpcurl -plaintext "${PROTO_ARGS[@]}" -d '{"user_id": 2}' $HOST userservice.UserService/GetUser > /dev/null 2>&1; then
                    ((count++))
                else
                    ((errors++))
                fi
                ;;
            3)
                # GetUser (non-existent)
                if grpcurl -plaintext "${PROTO_ARGS[@]}" -d '{"user_id": 9999}' $HOST userservice.UserService/GetUser > /dev/null 2>&1; then
                    ((count++))
                else
                    ((errors++))
                fi
                ;;
        esac
    done

    echo "$count $errors"
}

echo "Starting stress test..."
echo ""

# Record start time
start_time=$(date +%s)
end_time=$((start_time + DURATION))

# Launch workers in parallel
pids=()
tmpdir=$(mktemp -d)
for i in $(seq 1 $CONCURRENCY); do
    run_worker $i $end_time > "$tmpdir/worker_$i.txt" &
    pids+=($!)
done

# Wait for all workers
for pid in "${pids[@]}"; do
    wait $pid
done

# Calculate elapsed time
actual_end=$(date +%s)
elapsed=$((actual_end - start_time))

# Aggregate results
total_requests=0
total_errors=0
for i in $(seq 1 $CONCURRENCY); do
    result=$(cat "$tmpdir/worker_$i.txt")
    requests=$(echo $result | cut -d' ' -f1)
    errors=$(echo $result | cut -d' ' -f2)
    total_requests=$((total_requests + requests))
    total_errors=$((total_errors + errors))
done

# Clean up
rm -rf "$tmpdir"

# Calculate throughput
if [ $elapsed -gt 0 ]; then
    rps=$((total_requests / elapsed))
else
    rps=$total_requests
fi

echo "=============================================="
echo "Results"
echo "=============================================="
echo "Total Requests:    $total_requests"
echo "Total Errors:      $total_errors"
echo "Elapsed Time:      ${elapsed}s"
echo "Throughput:        $rps req/s"
echo "Avg Latency:       ~$((elapsed * 1000 * CONCURRENCY / (total_requests + 1)))ms (estimated)"
echo ""

# Quick single-request latency test
echo "Single request latency sample:"
time grpcurl -plaintext "${PROTO_ARGS[@]}" -d '{"user_id": 1}' $HOST userservice.UserService/GetUser > /dev/null

echo ""
echo "Stress test complete!"
