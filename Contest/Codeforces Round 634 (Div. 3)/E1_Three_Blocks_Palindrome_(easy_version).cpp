#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
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
 const int M = 201, N = 2e5 + 10;
int arr[N], n;
vector<int> cnt(M);
 void input(){
    cin >> n;
    fill(all(cnt), 0);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        cnt[arr[i]]++;
    }
}
 void solve()
{
    input();
    int ans = 1;
    for(int num = 1; num < M; num++){
        if(cnt[num] == 0)
            continue;
        multiset<int> ms;
        vector<int> tmp = cnt;
        for(auto &x: tmp){
            if(x)
                ms.insert(x);
        }
        int i = 0, j = n - 1, sym = 0;
        while(i < j){
            while(i <= j and arr[i] != num){
                ms.erase(ms.find(tmp[arr[i]]));
                tmp[arr[i]]--;
                if(tmp[arr[i]])
                    ms.insert(tmp[arr[i]]);
                i++;
            }
            while(j >= i and arr[j] != num){
                ms.erase(ms.find(tmp[arr[j]]));
                tmp[arr[j]]--;
                if(tmp[arr[j]])
                    ms.insert(tmp[arr[j]]);
                j--;
            }
            if(i > j)
                break;
            sym++;
            if(i == j)
                ans = max(ans, 2 * sym - 1);
            ms.erase(ms.find(tmp[arr[i]]));
            tmp[arr[i]]--;
            if(tmp[arr[i]])
                ms.insert(tmp[arr[i]]);
            i++;
            if(i <= j){
                ms.erase(ms.find(tmp[arr[j]]));
                tmp[arr[j]]--;
                if(tmp[arr[j]])
                    ms.insert(tmp[arr[j]]);
                j--;
                ans = max(ans, 2 * sym + (ms.empty() ? 0 : *ms.rbegin()));
            }
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