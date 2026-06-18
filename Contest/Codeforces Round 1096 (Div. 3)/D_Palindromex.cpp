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
 const int N = 2e5 + 10;
int arr[N], n;
 bool possible(int start){
    set<int> available;
    available.insert(arr[start]);
    for(int i = start + 1; i < 2 * n; i++){
        int j = start - (i - start);
        if(j < 0 or arr[i] != arr[j])
            break;
        available.insert(arr[i]);
    }
    int mex = 0;
    for(auto &x: available){
        if(x == mex)
            mex++;
    }
    return mex > arr[start];
}
 bool possible(int l, int r){
    set<int> available;
    for(int i = l, j = r; i <= j; i++, j--){
        if(arr[i] != arr[j])
            return false;
        available.insert(arr[i]);
    }
    for(int i = r + 1; i < 2 * n; i++){
        int j = l - (i - r);
        if(j < 0 or arr[i] != arr[j])
            break;
        available.insert(arr[i]);
    }
    int mex = 0;
    for(auto &x: available){
        if(x == mex)
            mex++;
    }
    return mex > arr[l];
}
 void solve()
{
    cin >> n;
    vector<vector<int>> pos(n);
    for(int i = 0; i < 2 * n; i++){
        cin >> arr[i];
        pos[arr[i]].push_back(i);
    }
    int l = 1, r = n, ans = 1;
    while(l <= r){
        int mid = (l + r) / 2;
        if(possible(pos[mid - 1][0]) or possible(pos[mid - 1][1]) or 
            possible(pos[mid - 1][0], pos[mid - 1][1])){
            ans = mid;
            l = mid + 1;
        }else{
            r = mid - 1;
        }
    }
    cout << ans << endl;
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