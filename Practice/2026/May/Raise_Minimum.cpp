#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int unsigned long long
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

bool check(vector<int> &arr, int target, int &k, int &n){
    int op = 0;
    for(int i = 0; i < n; i++){
        if(arr[i] >= target)
            continue;
        int need = (target - arr[i] + i) / (i + 1);
        op += need;
    }
    return op <= k;
}

void solve()
{
    int n, k;
    cin >> n >> k;
    vector<int> arr(n);
    for(int i = 0; i < n; i++)
        cin >> arr[i];

    int l = 1, r = 2e18 + 10;
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(arr, mid, k, n))
            l = mid + 1;
        else
            r = mid - 1;
    }
    cout << r << endl;
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