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

int even_query(vector<int> arr, int &n, int k){
    for(int i = 0; i < n; i++){
        arr[i] += (k - i);
    }
    k -= n;
    int mn = *min_element(all(arr)), sum = accumulate(all(arr), 0ll);
    int extra = sum - n * mn;
    if(extra * 2 >= k){
        return mn;
    }
    k -= extra * 2;
    k /= 2;
    return mn - (k + n - 1) / n;
}

int odd_query(vector<int> arr, int &n, int k){
    for(int i = 0; i < n - 1; i++){
        arr[i] += (k - i);
    }
    k -= n - 1;
    int mn = *min_element(all(arr)), sum = accumulate(all(arr), 0ll);
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
    vector<int> arr(n);
    for(auto &x: arr)
        cin >> x;
    sort(all(arr));
    while(q--){
        cin >> k;
        if(k < n){
            int mn = inf;
            for(int i = 0; i < k; i++){
                mn = min(mn, arr[i] + k - i);
            }
            cout << min(mn, *min_element(arr.begin() + k, arr.end())) << endl;
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