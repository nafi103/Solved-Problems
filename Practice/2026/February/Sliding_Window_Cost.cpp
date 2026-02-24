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
    int n, k;
    cin >> n >> k;
    multiset<int> left, right;
    int left_sum = 0, right_sum = 0, half = (k + 1) / 2;
    int arr[n + 1];
    for(int i = 1; i <= n; i++){
        int &x = arr[i];
        cin >> x;
        if(i > k){
            int rm = arr[i - k];
            if(left.count(rm)){
                left.erase(left.find(rm));
                left_sum -= rm;
                if(sz(right)){
                    int add = *right.begin();
                    left_sum += add;
                    left.insert(add);
                    right_sum -= add;
                    right.erase(right.begin());
                }
            }else{
                right.erase(right.find(rm));
                right_sum -= rm;
            }
        }
        left.insert(x);
        left_sum += x;
        if(sz(left) > half){
            auto it = left.rbegin();
            left_sum -= *it;
            right.insert(*it);
            right_sum += *it;
            left.erase(left.find(*it));
        }
        if(i >= k){
            int median = *left.rbegin();
            cout << sz(left) * median - left_sum + right_sum - sz(right) * median;
            cout << (i == n ? '\n' : ' ');
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