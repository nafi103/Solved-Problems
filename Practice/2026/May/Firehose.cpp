#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e6;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

bool check(int d, vector<int> &arr, int k){
    int curr = -inf, cnt = 0;
    for(auto &x: arr){
        if(abs(x - curr) > d){
            cnt++;
            curr = x + d;
        }
    }

    if(cnt <= k)
        return true;

    cnt = 1; curr = (arr[0] - d + mod) % mod;

    for(int i = sz(arr) - 1; i > 0; i--){
        if(abs(arr[i] - curr) > d){
            cnt++;
            curr = arr[i] - d;
        }
    }

    return cnt <= k;
}

void solve()
{
    int n, k;
    cin >> n;
    vector<int> arr(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    sort(all(arr));
    cin >> k;
    int l = 0, r = 1e9 + 10;
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(mid, arr, k))
            r = mid - 1;
        else
            l = mid + 1;
    }
    cout << l << endl;
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