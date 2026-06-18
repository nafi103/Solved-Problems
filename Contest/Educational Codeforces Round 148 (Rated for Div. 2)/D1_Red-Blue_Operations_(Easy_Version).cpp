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
 int arr_sum = 0, mn_rel_skip = inf, mn_rel = inf;
 int f(int n){
    return (n * (n + 1)) / 2;
}
 int even_query(vector<int> &arr, int &n, int k){
    // Need to solve this in O(1) or O(logn)
    // for(int i = 0; i < n; i++){
    //     arr[i] += (k - i);
    // }
    // int mn = *min_element(all(arr));
    int mn = mn_rel + k;
     // sum part is just arr[i] + arithmetic progression
    int sum = arr_sum + f(k) - f(k - n);
    k -= n;
    int extra = sum - n * mn;
    if(extra * 2 >= k){
        return mn;
    }
    k -= extra * 2;
    k /= 2;
    return mn - (k + n - 1) / n;
}
 int odd_query(vector<int> &arr, int &n, int k){
    // for(int i = 0; i < n - 1; i++){
    //     arr[i] += (k - i);
    // }
    // int mn = *min_element(all(arr));
    int mn = min(mn_rel_skip + k, arr[n - 1]);
     int sum = arr_sum + f(k) - f(k - n + 1);
    k -= n - 1;
    int extra = sum - n * mn;
    if(extra * 2 >= k){
        return mn;
    }
    k -= extra * 2;
    k /= 2;
    return mn - (k + n - 1) / n;
}
 void solve()
{
    int n, q, k;
    cin >> n >> q;
    vector<int> arr(n), rel_arr(n), pre(n);
    for(auto &x: arr){
        cin >> x;
        arr_sum += x;
    }
        sort(all(arr));
    rel_arr = arr;
    for(int i = 1; i < n; i++)
        rel_arr[i] -= i;
    for(int i = 0; i < n - 1; i++){
        mn_rel = min(mn_rel, rel_arr[i]);
    }
    mn_rel_skip = mn_rel;
    mn_rel = min(mn_rel, rel_arr[n - 1]);
     //precalculate
    multiset<int> ms;
    for(auto &x: arr)
        ms.insert(x);
    for(int i = 0, rmn = inf; i < n - 1; i++){
        rmn = min(rmn, rel_arr[i]);
        ms.erase(ms.find(arr[i]));
        debug(rmn)
        pre[i] = min(rmn + i + 1, *ms.begin());
    }
     while(q--){
        cin >> k;
        if(k < n){
            //precalculate
            // int mn = inf;
            // for(int i = 0; i < k; i++){
            //     mn = min(mn, arr[i] + k - i);
            // }
            // cout << min(mn, *min_element(arr.begin() + k, arr.end())) << endl;
            cout << pre[k - 1] << endl;
        }else if((k - n) % 2 == 0){
            cout << even_query(arr, n, k) << endl;
        }else{
            cout << odd_query(arr, n, k) << endl;
        }
    }
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