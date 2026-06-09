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

int cnt[1000001];

void solve()
{
    int n;
    cin >> n;
    vector<vector<int>> grid(n);
    for(int i = 0; i < n; i++){
        int k;
        cin >> k;
        grid[i].resize(k);
        for(auto &x: grid[i]){
            cin >> x;
            cnt[x]++;
        }
    }
    Mint ans = 0, n_2 = n, tmp;
    n_2 = inv(n_2);
    n_2 *= n_2;
    for(int i = 0; i < n; i++){
        int k = sz(grid[i]);
        for(auto &x: grid[i]){
            tmp = cnt[x];
            ans += n_2 * Mint(cnt[x]) * inv(Mint(k));
        }
    }
    cout << ans.v << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}