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
    int n, k, x, op = 0;
    cin >> n >> k;
    int mid = (n + 1) / 2, d = inf, l, r;
    vector<int> arr(n), diff(k);
    for(int i = 0; i < n; i++)
        cin >> arr[i];
    for(int i = 0; i < k; i++){
        cin >> diff[i];
        diff[i]--;
        if(abs(mid - diff[i] - 1) < d){
            d = abs(mid - diff[i] - 1);
            l = diff[i], r = diff[i];
        }
    }
    x = arr[diff[0]];
    int curr = x;
    while(l > 0 or r < n - 1){
        while(l > 0 and arr[l - 1] == curr)
            l--;
        while(r < n - 1 and arr[r + 1] == curr)
            r++;
        if(l > 0 or r < n - 1){
            op++;
            curr = curr ^ 1;
        }
    }
    if(curr != x)
        op++;
    cout << op << endl;
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