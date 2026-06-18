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
    int n, k;
    cin >> n >> k;
    vector<vector<int>> arr(n);
    for(int i = 0, l; i < n; i++){
        cin >> l;
        arr[i].resize(l);
        for(auto &x: arr[i])
            cin >> x;
    }
    vector<int> c(n);
    for(auto &x: c)
        cin >> x;
    int len = 0;
    for(int i = 0, m = sz(arr[i]); i < n; i++, m = sz(arr[i])){
        if(len + c[i] * m < k){
            len += (c[i] * m);
            continue;
        }
        k -= len;
        k %= m;
        int idx = (k - 1 + m) % m;
        cout << arr[i][idx] << endl;
        return;
    }
    cout << -1 << endl;
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