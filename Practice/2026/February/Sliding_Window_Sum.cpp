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
    int n, k, x, a, b, c;
    cin >> n >> k >> x >> a >> b >> c;
    vector<int> arr(n);
    int sum = x, xr = (k == 1 ? x: 0);
    arr[0] = x;
    for(int i = 1; i < n; i++){
        arr[i] = (arr[i - 1] * a + b) % c;
        sum += arr[i];
        if(i >= k)
            sum -= arr[i - k];
        if(i >= k - 1)
            xr ^= sum;
    }
    cout << xr << endl;
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