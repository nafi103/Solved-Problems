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
    int n, x, y;
    cin >> n;
 
    cin >> x >> y;
    int max_sum = x + y, min_sum = x + y;
    int max_diff = x - y, min_diff = x - y;
 
    cout << 0 << endl;
 
    for(int i = 1; i < n; i++){
        cin >> x >> y;
 
        max_sum = max(max_sum, x + y);
        min_sum = min(min_sum, x + y);
        max_diff = max(max_diff, x - y);
        min_diff = min(min_diff, x - y);
 
        cout << max(max_diff - min_diff, max_sum - min_sum) << endl;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}