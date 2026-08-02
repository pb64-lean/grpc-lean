CREATE TABLE IF NOT EXISTS users (
    id BIGSERIAL PRIMARY KEY,
    username VARCHAR(255) UNIQUE NOT NULL,
    email VARCHAR(255) NOT NULL,
    status INT NOT NULL DEFAULT 1
);

-- Test data: alice and bob share an email, charlie has a unique one
INSERT INTO users (username, email, status) VALUES
    ('alice', 'shared@example.com', 1),
    ('bob',   'shared@example.com', 1),
    ('carol', 'shared@example.com', 1),
    ('dave',  'unique@example.com', 1);
