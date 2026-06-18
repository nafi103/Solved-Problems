#include <bits/stdc++.h>
using namespace std;
 int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        int n, sum = 0;
        cin >> n;
        vector<pair<int, int>> v, v1;
        for (int i = 2; i * i <= n; i++)
        {
            if (n % i == 0)
            {
                int cnt = 0;
                while (n % i == 0)
                {
                    cnt++;
                    n /= i;
                }
                v.push_back(make_pair(cnt, i));
            }
        }
        if (n > 1)
            v.push_back(make_pair(1, n));
        sort(v.begin(), v.end());
        while(v[v.size()-1].first>0){
            int num = 1;
            for (int i = 0; i < v.size(); i++)
            {
                if(v[i].first>0){
                    v[i].first--;
                    num*=v[i].second;
                }
            }
            sum+=num;
        }
        cout<<sum<<endl;
    }
}