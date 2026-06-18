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
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    int ans = 0, mn = inf, mx_ans = 0;
    map<int,int> id;
    for(int i = n - 1; i >= 0; i--){
        if(arr[i] < mn){
            id[arr[i]] = i;
            mn = arr[i];
        }else{
            ans += arr[i] - mn;
            arr[i] = mn;
        }
    }
    mx_ans = ans;
    for(auto &[val, i]: id){
        int l = 0, r = i;
        while(l <= r){
            int mid = (l + r) / 2;
            if(arr[mid] == val)
                r = mid - 1;
            else
                l = mid + 1;
        }
        int inc = i - l;
        mx_ans = max(mx_ans, ans + inc);
    }
    cout << mx_ans << endl;
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