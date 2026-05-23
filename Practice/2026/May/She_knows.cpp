#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

/*
 * Mint (Modular Integer)
 * Time: O(1) for arithmetic, O(log mod) for inv/pow
 * Use: Automatic modular arithmetic to avoid overflow/missing modulo errors
 */
struct Mint {
    int v;
    explicit operator int() const { return v; }
    Mint() { v = 0; }
    Mint(int _v) : v(_v % mod) { v += (v < 0) * mod; }
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
Mint operator*(Mint a, Mint b) { return Mint(a.v * b.v); }
Mint &operator*=(Mint &a, Mint b) { return a = a * b; }

Mint pow(Mint a, int p) {
    assert(p >= 0);
    Mint res = 1;
    while (p > 0) {
        if (p & 1) res *= a;
        a *= a;
        p >>= 1;
    }
    return res;
}

Mint inv(Mint a) {
    assert(a.v != 0);
    return pow(a, mod - 2);
}

Mint operator/(Mint a, Mint b) { return a * inv(b); }

void solve()
{
    int n, m, k;
    cin >> n >> m >> k;

    auto is_corner = [&](int &r, int &c){
        if((r == 1 or r == n) and (c == 1 or c == m))
            return true;
        return false;
    };

    auto is_border = [&](int &r, int &c){
        return r == 1 or r == n or c == 1 or c == m;
    };

    int border = 0, sum = 0;
    for(int i = 0, x, y, c; i < k; i++){
        cin >> x >> y >> c;
        if(is_corner(x, y))
            continue;
        if(is_border(x, y)){
            border++;
            sum += c;
        }
    }

    if(border == 2 * (n + m - 4)){
        cout << (sum & 1 ? 0ll : pow(Mint(2), n * m - k).v) << endl;
    }else{
        cout << pow(Mint(2), n * m - k - 1).v << endl;
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}