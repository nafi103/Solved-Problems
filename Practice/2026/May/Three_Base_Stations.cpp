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

bool check(int len, vector<int> &arr, int n){
    int curr = arr[0];
    for(int i = 0; i < 3; i++){
        int next_pos = upper_bound(all(arr), curr + len) - arr.begin();
        if(next_pos == n)
            return true;

        curr = arr[next_pos];
    }
    return false;
}

void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n);
    for(int i = 0; i < n; i++)
        cin >> arr[i];
    sort(all(arr));
    arr.erase(unique(all(arr)), arr.end());
    n = sz(arr);

    int l = 0, r = 1e9;
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(mid, arr, n)){
            r = mid - 1;
        }else{
            l = mid + 1;
        }
    }

    double len = (double)l / 2.0;
    cout << len << endl;

    int curr = arr[0];
    for(int i = 0; i < 3; i++){
        cout << len + curr << " \n"[i == 2];

        int next_pos = upper_bound(all(arr), curr + l) - arr.begin();
        if(next_pos != n)
            curr = arr[next_pos];
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(6);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}