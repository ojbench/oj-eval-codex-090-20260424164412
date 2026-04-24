// Implementation for Problem 090 (ACMOJ 2208)
#ifndef SRC_HPP
#define SRC_HPP

#include <vector>
#include <stdexcept>
#include <iostream>
#include "fraction.hpp"

class matrix {
private:
    int m, n;
    fraction **data;

    void alloc(int rows, int cols) {
        if (rows <= 0 || cols <= 0) {
            m = n = 0;
            data = nullptr;
            return;
        }
        m = rows; n = cols;
        data = new fraction *[m];
        for (int i = 0; i < m; ++i) {
            data[i] = new fraction[n];
            for (int j = 0; j < n; ++j) data[i][j] = fraction(0);
        }
    }

public:
    matrix() : m(0), n(0), data(nullptr) {}

    matrix(int m_, int n_) { alloc(m_, n_); }

    matrix(const matrix &obj) {
        if (obj.m == 0 || obj.n == 0 || obj.data == nullptr) {
            m = n = 0; data = nullptr; return;
        }
        alloc(obj.m, obj.n);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                data[i][j] = obj.data[i][j];
    }

    matrix(matrix &&obj) noexcept {
        m = obj.m; n = obj.n; data = obj.data;
        obj.m = obj.n = 0; obj.data = nullptr;
    }

    ~matrix() {
        if (data) {
            for (int i = 0; i < m; ++i) delete[] data[i];
            delete[] data; data = nullptr;
        }
        m = n = 0;
    }

    matrix &operator=(const matrix &obj) {
        if (this == &obj) return *this;
        // free current
        if (data) {
            for (int i = 0; i < m; ++i) delete[] data[i];
            delete[] data; data = nullptr;
        }
        m = n = 0;
        if (obj.m == 0 || obj.n == 0 || obj.data == nullptr) return *this;
        alloc(obj.m, obj.n);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                data[i][j] = obj.data[i][j];
        return *this;
    }

    fraction &operator()(int i, int j) {
        // i: 1-based row; j: 0-based column
        if (i < 1 || i > m || j < 0 || j >= n || data == nullptr) {
            throw matrix_error();
        }
        return data[i - 1][j];
    }

    friend matrix operator*(const matrix &lhs, const matrix &rhs) {
        if (lhs.n == 0 || rhs.m == 0 || lhs.n != rhs.m) {
            throw matrix_error();
        }
        matrix res(lhs.m, rhs.n);
        for (int i = 0; i < lhs.m; ++i) {
            for (int k = 0; k < lhs.n; ++k) {
                fraction aik = lhs.data[i][k];
                for (int j = 0; j < rhs.n; ++j) {
                    res.data[i][j] = res.data[i][j] + aik * rhs.data[k][j];
                }
            }
        }
        return res;
    }

    matrix transposition() {
        if (m == 0 || n == 0 || data == nullptr) throw matrix_error();
        matrix t(n, m);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                t.data[j][i] = data[i][j];
        return t;
    }

    fraction determination() {
        if (m == 0 || n == 0 || data == nullptr || m != n) throw matrix_error();
        int sz = m;
        // Create a copy to perform elimination
        std::vector<std::vector<fraction>> a(sz, std::vector<fraction>(sz));
        for (int i = 0; i < sz; ++i)
            for (int j = 0; j < sz; ++j)
                a[i][j] = data[i][j];

        fraction det(1);
        bool sign_pos = true; // track row swaps
        for (int i = 0; i < sz; ++i) {
            int pivot = i;
            for (int r = i; r < sz; ++r) {
                if (!(a[r][i] == fraction(0))) { pivot = r; break; }
            }
            if (pivot != i) {
                std::swap(a[pivot], a[i]);
                sign_pos = !sign_pos;
            }
            if (a[i][i] == fraction(0)) {
                return fraction(0);
            }
            for (int r = i + 1; r < sz; ++r) {
                fraction factor = a[r][i] / a[i][i];
                if (a[r][i] == fraction(0)) continue;
                for (int c = i; c < sz; ++c) {
                    a[r][c] = a[r][c] - factor * a[i][c];
                }
            }
        }
        for (int i = 0; i < sz; ++i) det = det * a[i][i];
        if (!sign_pos) det = det * fraction(-1);
        return det;
    }

    int rows() const { return m; }
    int cols() const { return n; }
};

class resistive_network {
private:
    int interface_size, connection_size;
    matrix adjacency;  // A: m x n incidence-like matrix (+1/-1)
    matrix conduction; // C: m x m diagonal of conductances

public:
    resistive_network(int interface_size_, int connection_size_, int from[], int to[], fraction resistance[]) :
        interface_size(interface_size_), connection_size(connection_size_),
        adjacency(connection_size_, interface_size_), conduction(connection_size_, connection_size_) {
        // Build adjacency (incidence) and conduction matrices
        for (int e = 1; e <= connection_size; ++e) {
            int u = from[e - 1];
            int v = to[e - 1];
            // incidence: +1 at from, -1 at to
            adjacency(e, u - 1) = fraction(1);
            adjacency(e, v - 1) = fraction(-1);
            // conduction diagonal = 1 / R
            fraction g = fraction(1) / resistance[e - 1];
            conduction(e, e - 1) = g; // using operator()(row 1-based, col 0-based)
        }
    }

    ~resistive_network() = default;

    fraction get_equivalent_resistance(int interface_id1, int interface_id2) {
        // Using formula: Laplacian L = A^T C A
        matrix L = adjacency.transposition() * conduction * adjacency;
        // Build b with +1 at id1, -1 at id2, zero elsewhere; and enforce u_n = 0 via Schur complement (reduce L by removing last node)
        int n = interface_size;
        // Reduce to (n-1)x(n-1) by removing last node (since u_n = 0)
        matrix Lr(n - 1, n - 1);
        for (int i = 1; i <= n - 1; ++i)
            for (int j = 0; j < n - 1; ++j)
                Lr(i, j) = L(i, j);
        // Solve Lr * U = b_reduced where b has +1 at id1, -1 at id2
        std::vector<fraction> b(n - 1, fraction(0));
        if (interface_id1 <= n - 1) b[interface_id1 - 1] = b[interface_id1 - 1] + fraction(1);
        if (interface_id2 <= n - 1) b[interface_id2 - 1] = b[interface_id2 - 1] - fraction(1);
        // Solve linear system via Gaussian elimination (fraction exact)
        std::vector<std::vector<fraction>> Aaug(n - 1, std::vector<fraction>(n)); // n-1 cols + RHS
        for (int i = 0; i < n - 1; ++i) {
            for (int j = 0; j < n - 1; ++j) Aaug[i][j] = Lr(i + 1, j);
            Aaug[i][n - 1] = b[i];
        }
        // Eliminate
        for (int i = 0; i < n - 1; ++i) {
            int pivot = i;
            for (int r = i; r < n - 1; ++r) {
                if (!(Aaug[r][i] == fraction(0))) { pivot = r; break; }
            }
            if (!(Aaug[pivot][i] == fraction(0))) {
                if (pivot != i) std::swap(Aaug[pivot], Aaug[i]);
                for (int r = i + 1; r < n - 1; ++r) {
                    fraction factor = Aaug[r][i] / Aaug[i][i];
                    if (Aaug[r][i] == fraction(0)) continue;
                    for (int c = i; c <= n - 1; ++c) {
                        Aaug[r][c] = Aaug[r][c] - factor * Aaug[i][c];
                    }
                }
            }
        }
        // Back substitution
        std::vector<fraction> U(n - 1, fraction(0));
        for (int i = n - 2; i >= 0; --i) {
            fraction sum(0);
            for (int j = i + 1; j < n - 1; ++j) sum = sum + Aaug[i][j] * U[j];
            if (Aaug[i][i] == fraction(0)) throw resistive_network_error();
            U[i] = (Aaug[i][n - 1] - sum) / Aaug[i][i];
        }
        // Equivalent resistance = voltage difference between id1 and id2 when 1A injected at id1 and extracted at id2
        fraction u1(0), u2(0);
        if (interface_id1 <= n - 1) u1 = U[interface_id1 - 1];
        if (interface_id2 <= n - 1) u2 = U[interface_id2 - 1];
        return u1 - u2; // since u_n = 0 baseline
    }

    fraction get_voltage(int id, fraction current[]) {
        // Build Laplacian
        matrix L = adjacency.transposition() * conduction * adjacency;
        int n = interface_size;
        // Reduce and solve with u_n = 0
        matrix Lr(n - 1, n - 1);
        for (int i = 1; i <= n - 1; ++i)
            for (int j = 0; j < n - 1; ++j)
                Lr(i, j) = L(i, j);
        std::vector<fraction> b(n - 1, fraction(0));
        for (int i = 0; i < n - 1; ++i) b[i] = current[i];
        // Solve Lr * U = b
        std::vector<std::vector<fraction>> Aaug(n - 1, std::vector<fraction>(n));
        for (int i = 0; i < n - 1; ++i) {
            for (int j = 0; j < n - 1; ++j) Aaug[i][j] = Lr(i + 1, j);
            Aaug[i][n - 1] = b[i];
        }
        for (int i = 0; i < n - 1; ++i) {
            int pivot = i;
            for (int r = i; r < n - 1; ++r) if (!(Aaug[r][i] == fraction(0))) { pivot = r; break; }
            if (!(Aaug[pivot][i] == fraction(0))) {
                if (pivot != i) std::swap(Aaug[pivot], Aaug[i]);
                for (int r = i + 1; r < n - 1; ++r) {
                    fraction factor = Aaug[r][i] / Aaug[i][i];
                    if (Aaug[r][i] == fraction(0)) continue;
                    for (int c = i; c <= n - 1; ++c)
                        Aaug[r][c] = Aaug[r][c] - factor * Aaug[i][c];
                }
            }
        }
        std::vector<fraction> U(n - 1, fraction(0));
        for (int i = n - 2; i >= 0; --i) {
            fraction sum(0);
            for (int j = i + 1; j < n - 1; ++j) sum = sum + Aaug[i][j] * U[j];
            if (Aaug[i][i] == fraction(0)) throw resistive_network_error();
            U[i] = (Aaug[i][n - 1] - sum) / Aaug[i][i];
        }
        return U[id - 1];
    }

    fraction get_power(fraction voltage[]) {
        // Power = U^T * L * U where L = A^T C A
        matrix L = adjacency.transposition() * conduction * adjacency;
        int n = interface_size;
        // Compute W = L * U
        matrix Umat(n, 1);
        for (int i = 1; i <= n; ++i) Umat(i, 0) = voltage[i - 1];
        matrix W = L * Umat;
        // P = sum_i U_i * W_i
        fraction P(0);
        for (int i = 1; i <= n; ++i) P = P + voltage[i - 1] * W(i, 0);
        return P;
    }
};

#endif // SRC_HPP

