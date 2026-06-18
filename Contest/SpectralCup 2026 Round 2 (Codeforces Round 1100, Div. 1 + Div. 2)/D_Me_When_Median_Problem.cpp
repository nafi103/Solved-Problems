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
 const int N = 1e5 + 10;
int a[N], b[N], n;
 bool check(int target){
    vector<int> arr;
    for(int i = 0; i < n; i++){
        int cnt = 0;
        if(a[i] >= target)
            cnt++;
        if(b[i] >= target)
            cnt++;
        if(cnt == 0 and (arr.empty() or arr.back() == 1)){
            arr.push_back(0);
        }else if(cnt == 2){
            arr.push_back(1);
        }
    }
     return count(all(arr), 1) > count(all(arr), 0);
}
 int bs(int l, int r){
    if(l > r)
        return r;
    int mid = (l + r) / 2;
    if(check(mid))
        return bs(mid + 1, r);
    return bs(l, mid - 1);
}
 void solve()
{
    cin >> n;
    for(int i = 0; i < n; i++)
        cin >> a[i];
    for(int i = 0; i < n; i++)
        cin >> b[i];
     cout << bs(1, 2 * n) << endl;
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