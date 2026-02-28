#pragma once
#ifndef SJTU_BIGINTEGER
#define SJTU_BIGINTEGER

#include <complex>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>

namespace sjtu {

static const long long BASE = 1000000000LL;
static const int BASE_DIGITS = 9;

class int2048 {
private:
    std::vector<long long> d;
    bool neg;

    void trim() {
        while (d.size() > 1 && d.back() == 0) d.pop_back();
        if (d.size() == 1 && d[0] == 0) neg = false;
    }

    bool isZero() const { return d.size() == 1 && d[0] == 0; }

    static int cmpAbs(const std::vector<long long> &a, const std::vector<long long> &b) {
        if (a.size() != b.size()) return a.size() < b.size() ? -1 : 1;
        for (int i = (int)a.size()-1; i >= 0; i--)
            if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
        return 0;
    }

    static void trimV(std::vector<long long> &v) {
        while (v.size() > 1 && v.back() == 0) v.pop_back();
    }

    static std::vector<long long> addAbs(const std::vector<long long> &a, const std::vector<long long> &b) {
        int n = std::max(a.size(), b.size());
        std::vector<long long> r(n+1, 0);
        for (int i = 0; i < n; i++) {
            if (i < (int)a.size()) r[i] += a[i];
            if (i < (int)b.size()) r[i] += b[i];
            if (r[i] >= BASE) { r[i+1] += r[i]/BASE; r[i] %= BASE; }
        }
        trimV(r);
        return r;
    }

    static std::vector<long long> subAbs(const std::vector<long long> &a, const std::vector<long long> &b) {
        std::vector<long long> r(a.size(), 0);
        long long borrow = 0;
        for (int i = 0; i < (int)a.size(); i++) {
            r[i] = a[i] - (i < (int)b.size() ? b[i] : 0) - borrow;
            if (r[i] < 0) { r[i] += BASE; borrow = 1; } else borrow = 0;
        }
        trimV(r);
        return r;
    }

    // ===== NTT =====
    static const int MOD1 = 998244353;
    static const int MOD2 = 985661441;
    static const int MOD3 = 754974721;

    static long long power(long long a, long long b, long long mod) {
        long long r = 1; a %= mod;
        for (; b > 0; b >>= 1) { if (b&1) r = r*a%mod; a = a*a%mod; }
        return r;
    }

    static void ntt(std::vector<long long> &a, bool inv, int mod) {
        int n = a.size();
        int g = (mod == MOD3) ? 11 : 3;
        for (int i = 1, j = 0; i < n; i++) {
            int bit = n >> 1;
            for (; j & bit; bit >>= 1) j ^= bit;
            j ^= bit;
            if (i < j) std::swap(a[i], a[j]);
        }
        for (int len = 2; len <= n; len <<= 1) {
            long long w = inv ? power(g, mod-1-(mod-1)/len, mod) : power(g, (mod-1)/len, mod);
            for (int i = 0; i < n; i += len) {
                long long wn = 1;
                for (int j = 0; j < len/2; j++) {
                    long long u = a[i+j], v = a[i+j+len/2]*wn%mod;
                    a[i+j] = (u+v)%mod;
                    a[i+j+len/2] = (u-v+mod)%mod;
                    wn = wn*w%mod;
                }
            }
        }
        if (inv) { long long inv_n = power(n, mod-2, mod); for (auto &x:a) x = x*inv_n%mod; }
    }

    static std::vector<long long> mulNTT(const std::vector<long long> &a, const std::vector<long long> &b) {
        int rsz = a.size() + b.size() - 1;
        int n = 1; while (n < rsz) n <<= 1;
        
        auto doNTT = [&](int mod) -> std::vector<long long> {
            std::vector<long long> fa(n,0), fb(n,0);
            for (int i = 0; i < (int)a.size(); i++) fa[i] = a[i] % mod;
            for (int i = 0; i < (int)b.size(); i++) fb[i] = b[i] % mod;
            ntt(fa, false, mod); ntt(fb, false, mod);
            for (int i = 0; i < n; i++) fa[i] = fa[i]*fb[i]%mod;
            ntt(fa, true, mod);
            return fa;
        };
        
        auto r1 = doNTT(MOD1), r2 = doNTT(MOD2), r3 = doNTT(MOD3);
        long long m1 = MOD1, m2 = MOD2, m3 = MOD3;
        long long m1inv2 = power(m1, m2-2, m2);
        long long m12inv3 = power((long long)m1%m3 * (m2%m3) % m3, m3-2, m3);
        
        std::vector<long long> result(rsz);
        __int128 carry = 0;
        for (int i = 0; i < rsz; i++) {
            long long a1 = r1[i];
            long long a2 = (r2[i] - a1%m2 + m2) % m2 * m1inv2 % m2;
            long long vm3 = (a1 + (__int128)a2*m1) % m3;
            long long a3 = ((r3[i] - vm3 + m3) % m3) * m12inv3 % m3;
            __int128 val = a1 + (__int128)a2*m1 + (__int128)a3*m1*m2 + carry;
            result[i] = (long long)(val % BASE);
            carry = val / BASE;
        }
        while (carry > 0) { result.push_back((long long)(carry%BASE)); carry /= BASE; }
        trimV(result);
        return result;
    }

    static std::vector<long long> mulSimple(const std::vector<long long> &a, const std::vector<long long> &b) {
        int n = a.size() + b.size() + 1;
        std::vector<long long> r(n, 0);
        for (int i = 0; i < (int)a.size(); i++) {
            __int128 carry = 0;
            for (int j = 0; j < (int)b.size(); j++) {
                __int128 cur = (__int128)a[i]*b[j] + r[i+j] + carry;
                r[i+j] = (long long)(cur % BASE);
                carry = cur / BASE;
            }
            for (int k = i+(int)b.size(); carry; k++) {
                __int128 cur = r[k] + carry;
                r[k] = (long long)(cur % BASE);
                carry = cur / BASE;
            }
        }
        trimV(r);
        return r;
    }

    static std::vector<long long> mulDigits(const std::vector<long long> &a, const std::vector<long long> &b) {
        if ((a.size()==1 && a[0]==0) || (b.size()==1 && b[0]==0)) return {0};
        if (a.size() <= 64 || b.size() <= 64) return mulSimple(a, b);
        return mulNTT(a, b);
    }

    // ===== Division =====
    
    static std::vector<long long> mulScalar(const std::vector<long long> &a, long long s) {
        if (s == 0) return {0};
        std::vector<long long> r(a.size()+2, 0);
        __int128 carry = 0;
        for (int i = 0; i < (int)a.size(); i++) {
            __int128 cur = (__int128)a[i]*s + carry;
            r[i] = (long long)(cur % BASE);
            carry = cur / BASE;
        }
        int k = a.size();
        while (carry) { r[k++] = (long long)(carry % BASE); carry /= BASE; }
        trimV(r);
        return r;
    }
    
    static std::vector<long long> divSchool(const std::vector<long long> &a, const std::vector<long long> &b) {
        int n = a.size(), m = b.size();
        if (cmpAbs(a, b) < 0) return {0};
        if (m == 1) {
            std::vector<long long> q(n, 0);
            __int128 rem = 0;
            for (int i = n-1; i >= 0; i--) {
                __int128 cur = rem * BASE + a[i];
                q[i] = (long long)(cur / b[0]);
                rem = cur % b[0];
            }
            trimV(q);
            return q;
        }
        
        long long f = BASE / (b.back() + 1);
        auto aa = mulScalar(a, f);
        auto bb = mulScalar(b, f);
        int mm = bb.size();
        
        int needed = std::max((int)aa.size(), mm) + 2;
        aa.resize(needed, 0);
        
        int qlen = (int)aa.size() - mm;
        std::vector<long long> q(qlen, 0);
        
        for (int i = qlen - 1; i >= 0; i--) {
            if (i + mm >= (int)aa.size()) continue;
            
            __int128 top = (__int128)aa[i+mm] * BASE + aa[i+mm-1];
            long long qhat = (long long)(top / bb[mm-1]);
            long long rhat = (long long)(top % bb[mm-1]);
            
            while (qhat >= BASE || 
                   (mm >= 2 && (__int128)qhat * bb[mm-2] > (__int128)rhat * BASE + aa[i+mm-2])) {
                qhat--;
                rhat += bb[mm-1];
                if (rhat >= BASE) break;
            }
            
            __int128 carry = 0;
            for (int j = 0; j < mm; j++) {
                __int128 prod = (__int128)qhat * bb[j];
                long long cur = aa[i+j] - (long long)carry - (long long)(prod % BASE);
                carry = prod / BASE;
                if (cur < 0) { cur += BASE; carry++; }
                aa[i+j] = cur;
            }
            if (i+mm < (int)aa.size()) aa[i+mm] -= (long long)carry;
            
            q[i] = qhat;
            
            if (i+mm < (int)aa.size() && aa[i+mm] < 0) {
                q[i]--;
                long long c = 0;
                for (int j = 0; j < mm; j++) {
                    long long sum = aa[i+j] + bb[j] + c;
                    if (sum >= BASE) { sum -= BASE; c = 1; } else c = 0;
                    aa[i+j] = sum;
                }
                if (i+mm < (int)aa.size()) aa[i+mm] += c;
            }
        }
        
        trimV(q);
        return q;
    }
    
    static std::vector<long long> shiftRight(const std::vector<long long> &a, int k) {
        if (k >= (int)a.size()) return {0};
        std::vector<long long> r(a.begin()+k, a.end());
        trimV(r);
        return r;
    }
    
    static std::vector<long long> shiftLeft(const std::vector<long long> &a, int k) {
        if (a.size()==1 && a[0]==0) return {0};
        std::vector<long long> r(k + a.size(), 0);
        for (int i = 0; i < (int)a.size(); i++) r[i+k] = a[i];
        return r;
    }
    
    // Newton's method to compute floor(B^{2m} / b)
    // We iterate: x_{k+1} = 2*x_k - floor(b * x_k^2 / B^{2m})
    // Working at full precision throughout (using b, not truncated b).
    // Start with a rough estimate and iterate until convergence.
    static std::vector<long long> newtonRecip(const std::vector<long long> &b, int m) {
        // Initial estimate: use top 2 digits for better accuracy
        __int128 b_top;
        if (m >= 2) {
            b_top = (__int128)b[m-1] * BASE + b[m-2];
        } else {
            b_top = b[m-1];
        }
        
        // x0 ≈ B^{2m} / b ≈ B^{2m} / (b_top * B^{m-2}) = B^{m+2} / b_top (if m >= 2)
        // or B^{2m} / (b_top * B^{m-1}) = B^{m+1} / b_top (if m == 1)
        
        // Actually, let's compute x0 more carefully.
        // B^{2m} / b. b ≈ b_top_k * B^{m-k} where b_top_k uses top k digits.
        // So B^{2m}/b ≈ B^{m+k}/b_top_k
        // For k=2: B^{m+2}/b_top_2
        
        // x0 = floor(B^4 / b_top_2) * B^{m-2} (for m >= 2)
        __int128 x0_high;
        int x0_shift;
        if (m >= 2) {
            // B^4 / b_top_2 where b_top_2 = b[m-1]*B + b[m-2]
            // B^4 = 10^36, fits in __int128
            __int128 B4 = (__int128)BASE * BASE * BASE * BASE;
            x0_high = B4 / b_top;
            x0_shift = m - 2;
        } else {
            __int128 B2 = (__int128)BASE * BASE;
            x0_high = B2 / b_top;
            x0_shift = 0;
        }
        
        // Convert x0_high to digit vector
        std::vector<long long> x;
        {
            __int128 v = x0_high;
            if (v == 0) x.push_back(0);
            else while (v > 0) { x.push_back((long long)(v % BASE)); v /= BASE; }
        }
        if (x0_shift > 0) x = shiftLeft(x, x0_shift);
        
        // Newton iterations: x = 2*x - floor(b * x^2 / B^{2m})
        // We iterate until convergence (x doesn't change)
        for (int iter = 0; iter < 100; iter++) {
            auto bx = mulDigits(b, x);
            // bx should be close to B^{2m}
            // 2*B^{2m} - bx
            std::vector<long long> two_B(2*m+1, 0);
            two_B[2*m] = 2;
            
            std::vector<long long> residual;
            if (cmpAbs(two_B, bx) > 0) {
                residual = subAbs(two_B, bx);
            } else {
                // bx >= 2*B^{2m}: x is too large
                // Set residual = 0 and fall back
                residual = {0};
            }
            
            auto x_full = mulDigits(x, residual);
            auto x_new = shiftRight(x_full, 2*m);
            
            if (cmpAbs(x_new, x) == 0 || (x_new.size() == 1 && x_new[0] == 0)) break;
            x = x_new;
        }
        
        // Final adjustment: ensure x * b <= B^{2m} < (x+1) * b
        auto check = mulDigits(x, b);
        std::vector<long long> B2m(2*m+1, 0);
        B2m[2*m] = 1;
        
        while (cmpAbs(check, B2m) > 0) {
            x = subAbs(x, {1});
            check = subAbs(check, b);
        }
        auto next = addAbs(check, b);
        while (cmpAbs(next, B2m) <= 0) {
            x = addAbs(x, {1});
            check = next;
            next = addAbs(check, b);
        }
        
        return x;
    }
    
    static std::vector<long long> divDigits(const std::vector<long long> &a, const std::vector<long long> &b) {
        int cmp = cmpAbs(a, b);
        if (cmp < 0) return {0};
        if (cmp == 0) return {1};
        
        int m = b.size();
        
        if (m <= 500) {
            return divSchool(a, b);
        }
        
        // Newton-based
        auto inv = newtonRecip(b, m);
        auto q_full = mulDigits(a, inv);
        auto q = shiftRight(q_full, 2*m);
        
        auto qb = mulDigits(q, b);
        
        while (cmpAbs(qb, a) > 0) {
            q = subAbs(q, {1});
            qb = subAbs(qb, b);
        }
        
        auto rem = subAbs(a, qb);
        while (cmpAbs(rem, b) >= 0) {
            rem = subAbs(rem, b);
            q = addAbs(q, {1});
        }
        
        trimV(q);
        return q;
    }

    void doAdd(const int2048 &other) {
        if (neg == other.neg) {
            d = addAbs(d, other.d);
        } else {
            int c = cmpAbs(d, other.d);
            if (c == 0) { d = {0}; neg = false; }
            else if (c > 0) { d = subAbs(d, other.d); }
            else { d = subAbs(other.d, d); neg = other.neg; }
        }
        trim();
    }

    void doSub(const int2048 &other) {
        bool flipped = other.isZero() ? other.neg : !other.neg;
        if (neg == flipped) {
            d = addAbs(d, other.d);
        } else {
            int c = cmpAbs(d, other.d);
            if (c == 0) { d = {0}; neg = false; }
            else if (c > 0) { d = subAbs(d, other.d); }
            else { d = subAbs(other.d, d); neg = flipped; }
        }
        trim();
    }

public:
    int2048() : d(1, 0), neg(false) {}

    int2048(long long v) : neg(false) {
        if (v < 0) {
            neg = true;
            unsigned long long uv = (unsigned long long)(-(v+1)) + 1ULL;
            while (uv > 0) { d.push_back((long long)(uv % BASE)); uv /= BASE; }
        } else if (v == 0) {
            d.push_back(0);
        } else {
            while (v > 0) { d.push_back(v % BASE); v /= BASE; }
        }
        if (d.empty()) d.push_back(0);
        trim();
    }

    int2048(const std::string &s) : neg(false) { read(s); }
    int2048(const int2048 &o) : d(o.d), neg(o.neg) {}

    void read(const std::string &s) {
        d.clear(); neg = false;
        int start = 0;
        if (!s.empty() && s[0] == '-') { neg = true; start = 1; }
        else if (!s.empty() && s[0] == '+') { start = 1; }
        while (start < (int)s.size()-1 && s[start] == '0') start++;
        int end = s.size();
        for (int i = end; i > start; i -= BASE_DIGITS) {
            int from = std::max(start, i - BASE_DIGITS);
            long long val = 0;
            for (int j = from; j < i; j++) val = val*10 + (s[j]-'0');
            d.push_back(val);
        }
        if (d.empty()) d.push_back(0);
        trim();
    }

    void print() {
        if (neg) putchar('-');
        printf("%lld", d.back());
        for (int i = (int)d.size()-2; i >= 0; i--) printf("%09lld", d[i]);
    }

    int2048 &add(const int2048 &o) { doAdd(o); return *this; }
    friend int2048 add(int2048 a, const int2048 &b) { a.doAdd(b); return a; }
    int2048 &minus(const int2048 &o) { doSub(o); return *this; }
    friend int2048 minus(int2048 a, const int2048 &b) { a.doSub(b); return a; }

    int2048 operator+() const { return *this; }
    int2048 operator-() const { int2048 r(*this); if (!r.isZero()) r.neg = !r.neg; return r; }

    int2048 &operator=(const int2048 &o) { if (this != &o) { d = o.d; neg = o.neg; } return *this; }

    int2048 &operator+=(const int2048 &o) { doAdd(o); return *this; }
    friend int2048 operator+(int2048 a, const int2048 &b) { a += b; return a; }

    int2048 &operator-=(const int2048 &o) { doSub(o); return *this; }
    friend int2048 operator-(int2048 a, const int2048 &b) { a -= b; return a; }

    int2048 &operator*=(const int2048 &o) {
        if (isZero() || o.isZero()) { d = {0}; neg = false; return *this; }
        bool rn = neg != o.neg;
        d = mulDigits(d, o.d);
        neg = rn;
        trim();
        return *this;
    }
    friend int2048 operator*(int2048 a, const int2048 &b) { a *= b; return a; }

    int2048 &operator/=(const int2048 &o) {
        if (isZero()) return *this;
        bool rn = neg != o.neg;
        auto ad = d, bd = o.d;
        auto q = divDigits(ad, bd);
        if (rn) {
            auto qb = mulDigits(q, bd);
            if (cmpAbs(qb, ad) != 0) q = addAbs(q, {1});
        }
        d = q;
        neg = rn;
        trim();
        return *this;
    }
    friend int2048 operator/(int2048 a, const int2048 &b) { a /= b; return a; }

    int2048 &operator%=(const int2048 &o) {
        int2048 q = *this / o;
        *this -= q * o;
        return *this;
    }
    friend int2048 operator%(int2048 a, const int2048 &b) { a %= b; return a; }

    friend std::istream &operator>>(std::istream &is, int2048 &v) {
        std::string s; is >> s; v.read(s); return is;
    }

    friend std::ostream &operator<<(std::ostream &os, const int2048 &v) {
        if (v.neg) os << '-';
        os << v.d.back();
        char pf = os.fill('0');
        for (int i = (int)v.d.size()-2; i >= 0; i--) { os.width(BASE_DIGITS); os << v.d[i]; }
        os.fill(pf);
        return os;
    }

    friend bool operator==(const int2048 &a, const int2048 &b) { return a.neg == b.neg && a.d == b.d; }
    friend bool operator!=(const int2048 &a, const int2048 &b) { return !(a==b); }
    friend bool operator<(const int2048 &a, const int2048 &b) {
        if (a.neg != b.neg) return a.neg;
        int c = cmpAbs(a.d, b.d);
        return a.neg ? c > 0 : c < 0;
    }
    friend bool operator>(const int2048 &a, const int2048 &b) { return b < a; }
    friend bool operator<=(const int2048 &a, const int2048 &b) { return !(b < a); }
    friend bool operator>=(const int2048 &a, const int2048 &b) { return !(a < b); }
};

} // namespace sjtu

#endif
