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
 vector<int> 
add = {2, 3, 5, 7, 30, 42, 70, 105},
del = {6, 10, 14, 15, 21, 35, 210};
 void solve()
{
    int l, r;
    cin >> l >> r;
    int rbad = 0, lbad = 0;
    for(auto &x: add){
        rbad += r / x;
        lbad += (l - 1) / x;
    }
    for(auto &x: del){
        rbad -= r / x;
        lbad -= (l - 1) / x;
    }
    int range_bad = rbad - lbad;
    cout << (r - l + 1) - range_bad << endl;
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