#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 1e7 + 1;
vector<int> primes;
int phi[N], phi2[N];

void phi_1_to_n(){
    phi[1] = 1;
    for(int i = 2; i < N; i++) {
        if(phi[i] == 0){ 
            primes.push_back(i);
            phi[i] = i - 1;
        }
        for(int p : primes){
            if(i * p >= N) break;
            if(i % p == 0){
                phi[i * p] = phi[i] * p;
                break;
            }else {
                phi[i * p] = phi[i] * (p - 1);
            }
        }
    }
}

void phi_1_to_n2() {
    for (int i = 0; i < N; i++)
        phi2[i] = i;

    for (int i = 2; i < N; i++) {
        if (phi2[i] == i) {
            for (int j = i; j < N; j += i)
                phi2[j] -= phi2[j] / i;
        }
    }
}

struct Mint {
    int v;
    explicit operator int() const { return v; }
    Mint() { v = 0; }
    Mint(long long _v) : v(_v % mod) { v += (v < 0) * mod; }
};

Mint &operator+=(Mint &a, Mint b) {
    if ((a.v += b.v) >= mod) a.v -= mod;
    return a;
}

Mint &operator-=(Mint &a, Mint b) {
    if ((a.v -= b.v) < 0) a.v += mod;
    return a;
}

Mint operator+(Mint a, Mint b) { return a += b; }
Mint operator-(Mint a, Mint b) { return a -= b; }
Mint operator*(Mint a, Mint b) { return Mint((long long)a.v * b.v); }
Mint &operator*=(Mint &a, Mint b) { return a = a * b; }

Mint pow(Mint a, long long p) {
    assert(p >= 0);
    return p == 0 ? 1 : pow(a * a, p / 2) * (p & 1 ? a : 1);
}

Mint inv(Mint a) {
    assert(a.v != 0);
    return pow(a, mod - 2);
}

Mint operator/(Mint a, Mint b) { return a * inv(b); }

void solve()
{
    phi_1_to_n();
    phi_1_to_n2();
    for(int i = 1; i < N; i++){
        if(phi[i] != phi2[i]){
            cout << i << endl;
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}