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
    int n;
    cin >> n;
    vector<int> arr(n);
    for(auto &x: arr)
        cin >> x;
    arr.push_back(inf);

    int inc = 0;
    for(int i = 1; i < n; i++){
        if(arr[i] < arr[i - 1]){
            inc = max(inc, arr[i - 1] - arr[i]);
        }
    }

    for(int i = n - 1; i >= 0; i--){
        if(arr[i] + inc <= arr[i + 1])
            arr[i] += inc;
        if(arr[i] > arr[i + 1]){
            cout << "NO" << endl;
            return;
        }
    }

    cout << "YES" << endl;
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