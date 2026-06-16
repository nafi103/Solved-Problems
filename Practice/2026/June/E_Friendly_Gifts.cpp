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

const int N = 6001;
int range_min[N][N], range_max[N][N];
int n;

int get_ans(vector<int>&arr){
    vector<int> last_index(n + 1), mx(n);
    vector<bool> present(n + 1);
    for(int len = n / 2; len >= 1; len--){
        fill(all(last_index), -inf);
        fill(all(mx), -1);
        fill(all(present), false);
        int i = 0, j = 0;
        while(j < n){
            while(last_index[arr[j]] >= i){
                if(mx[i] != -1)
                    present[mx[i]] = true; 
                i++;
            }
            if(j - i + 1 == len){
                if(range_max[i][j] - range_min[i][j] + 1 == len){
                    mx[j] = range_max[i][j];
                    if(present[range_min[i][j] - 1]){
                        return len;
                    }
                }
            }
            last_index[arr[j]] = j;
            j++;
            while(j - i + 1 > len){
                if(mx[i] != -1)
                    present[mx[i]] = true; 
                i++;
            }
        }
    }

    return 0;
}

int get_solution(vector<int> &arr)
{
    for(int i = 0; i < n; i++){
        range_min[i][i] = range_max[i][i] = arr[i];
    }

    for(int len = 2; len <= n; len++){
        for(int j = len - 1, i; j < n; j++){
            i = j - len + 1;
            range_min[i][j] = min(range_min[i + 1][j], range_min[i][i]);
            range_max[i][j] = max(range_max[i + 1][j], range_max[i][i]);
        }
    }

    int ans = get_ans(arr);

    return ans;
}

void solve(){
    cin >> n;
    vector<int> arr(n);
    for(auto &x: arr)
        cin >> x;

    int ans = get_solution(arr);
    reverse(all(arr));
    ans = max(ans, get_solution(arr));

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