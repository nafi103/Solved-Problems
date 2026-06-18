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
    int n;
    cin >> n;
    string str;
    cin >> str;
     int sum = 0;
    Mint ans = 0, dp1 = 0, dp2 = 0;
    // dp1 -> valid subsequences ending with (
    // dp2 -> valid subsequences ending with )
     for(int i = 0; i < n; i++){
        if(str[i] == '('){
            sum += 1;
            ans += pow(Mint(2), i);
             Mint next_dp1 = dp1 * 2 + dp2 + 1;
            if(sum <= 1)
                next_dp1 = 0;
            dp1 = next_dp1;
        }
        else{
            sum -= 1;
            ans += dp1 + dp2 + 1;
             Mint next_dp1 = dp1;
            Mint next_dp2 = dp2 * 2 + dp1 + 1;
             if(sum <= 1)
                next_dp1 = 0;
            dp1 = next_dp1;
            dp2 = next_dp2;
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}