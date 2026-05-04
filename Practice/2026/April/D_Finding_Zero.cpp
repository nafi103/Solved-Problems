#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int query(vector<int> &arr){
    cout << "?";
    for(auto &x: arr)
        cout << " " << x;
    cout << endl;
    int res;
    cin >> res;
    return res;
}

void solve()
{
    int n;
    cin >> n;
    vector<int> arr = {1, 2, 3};
    int curr = query(arr);
    for(int i = 4; i <= n; i++){
        vector<int> arr1 = arr, arr2 = arr;
        arr1[0] = i;
        arr2[1] = i;
        int res1 = query(arr1), res2 = query(arr2);
        if(res1 < res2){
            swap(res1, res2);
            swap(arr1, arr2);
        }
        if(res1 >= curr){
            curr = res1;
            arr = arr1;
        }
    }
    set<int> s;
    for(auto &x: arr)
        s.insert(x);
    int ew;
    for(int i = 1; i <= n; i++)
        if(s.count(i) == 0){
            ew = i;
            break;
        }
    vector<int> ans;
    for(int j = 0; j < 3; j++){
        int xr = ew ^ arr[j];
        arr[j] = arr[j] ^ xr;
        int res = query(arr);
        if(res < curr)
            ans.push_back(arr[j] ^ xr);
        arr[j] = arr[j] ^ xr;
    }
    cout << "! " << ans[0] << " " << (sz(ans) == 2 ? ans[1]: ans[0]) << endl;
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