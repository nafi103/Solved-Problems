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
 void solve()
{
    int n, x;
    cin >> n >> x;
    int before_zero = x / 4 + 1;
    int before_one = (x + 2) / 4;
    int total_zero = (n + 1) / 4 + 1, total_one = (n + 3) / 4;
    int after_zero = total_zero - before_zero, after_one = total_one - before_one;
    after_one %= mod;
    before_zero%= mod;
    after_zero %= mod;
    before_one%= mod;
    int ans = (before_one * after_one) % mod;
    ans = (ans + (before_zero * after_zero) % mod) % mod;
    cout << (ans + mod) % mod << endl;
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