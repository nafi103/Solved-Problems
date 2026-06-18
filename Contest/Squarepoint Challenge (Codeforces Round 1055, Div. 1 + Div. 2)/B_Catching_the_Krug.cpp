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
    int n, bx, by, ax, ay;
    cin >> n >> bx >> by >> ax >> ay;
    int r = abs(ax - bx);
    int c = abs(ay - by);
    int r_rem = (bx < ax ? bx: n - bx);
    int c_rem = (by < ay ? by: n - by);
    if(r == 0)
        cout << c + c_rem << endl;
    else if(c == 0)
        cout << r + r_rem << endl;
    else
        cout << max(r + r_rem, c + c_rem) << endl;
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