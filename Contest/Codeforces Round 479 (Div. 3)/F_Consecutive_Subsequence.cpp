#include <bits/stdc++.h>
using namespace std;
#define int long long
#define Int int64_t
#define vi vector<int>
#define all(x) x.begin(), x.end()
bool cmp(vector<pair<int, int>> &a, vector<pair<int, int>> &b)
{
    int fa = a.size();
    int sa = b.size();
    return fa > sa;
}
void solve()
{
    int n;
    cin >> n;
    map<int, int> ans;
    int last = -1,size=0;
    vi arr(n+1);
    for (int i = 1; i <= n; i++)
    {
        int ele;
        cin >> ele;
        arr[i] = ele;
        // check that previous solution exist or not
        ans[ele] = ans[ele - 1] + 1;
        if(ans[ele] > size){
            size = ans[ele];
            last = ele;
        }
    }
    cout << size << endl;
     vector<int>elements;
    for (int i = n; i >= 1; i--) {
        if(arr[i] == last) {
            elements.push_back(i);
            last --;
        }
    }
    for(int i=elements.size()-1; i >= 0; i--){
        cout << elements[i] << " ";
    }
}
signed main()
{
    int tc = 1;
    // cin >> tc;
    for (int i = 1; i <= tc; i++)
    {
        solve();
    }
    return 0;
}